use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::{
    CurveGroup, VariableBaseMSM,
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, Field, UniformRand, Zero};
use ark_std::{log2, rand::RngCore};
use tiny_keccak::{Hasher, Shake};

use crate::{combine::affine_window_combine_one_endo, utils::absorb_curve};

pub struct Params<P: SWCurveConfig> {
    pub h: Vec<Affine<P>>,
    pub blinder_base: Affine<P>,
    // Has to be the same as the encryption base
    pub inner_product_base: Affine<P>,
}

pub struct ProverOutput<P: SWCurveConfig> {
    pub lr: Vec<(Affine<P>, Affine<P>)>,
    pub h0: Affine<P>,
    pub a0: P::ScalarField,
    pub public0: P::ScalarField,
    pub blinder: P::ScalarField,
}

impl<P: GLVConfig> Params<P> {
    pub fn new(prefix: &[u8], n: usize) -> Self {
        let n = 1 << log2(n);
        let h = (0..n).map(|i| random_group_element(prefix, i)).collect();
        let blinder_base = random_group_element(prefix, n);
        let inner_product_base = random_group_element(prefix, n + 1);
        Self {
            h,
            blinder_base,
            inner_product_base,
        }
    }

    pub fn prove<R: RngCore, S: CryptographicSponge>(
        &self,
        sponge: &mut S,
        rng: &mut R,
        mut a: Vec<P::ScalarField>,
        mut public: Vec<P::ScalarField>,
    ) -> ProverOutput<P> {
        let mut blinder = P::ScalarField::zero();
        let mut lr = vec![];

        // pad
        // assert_eq!(a.len(), public.len());
        let ceil_pow2 = 1 << log2(a.len());
        assert!(self.h.len() >= ceil_pow2);
        let mut h = self.h[..ceil_pow2].to_vec();
        let padding = (1 << log2(a.len())) as usize - a.len();
        a.extend((0..padding).map(|_| P::ScalarField::zero()));
        public.extend((0..padding).map(|_| P::ScalarField::zero()));

        let mut x_invs = vec![];
        while a.len() > 1 {
            let m = a.len() / 2;
            let l_blinder = P::ScalarField::rand(rng);
            let r_blinder = P::ScalarField::rand(rng);
            let z_l = inner_product(&a[m..], &public[..m]);
            let z_r = inner_product(&a[..m], &public[m..]);

            let l = <Projective<P> as VariableBaseMSM>::msm(&h[..m], &a[m..]).unwrap()
                + self.blinder_base * l_blinder
                + self.inner_product_base * z_l;
            let r = <Projective<P> as VariableBaseMSM>::msm(&h[m..], &a[..m]).unwrap()
                + self.blinder_base * r_blinder
                + self.inner_product_base * z_r;
            let l = l.into_affine();
            let r = r.into_affine();
            absorb_curve(sponge, &l);
            absorb_curve(sponge, &r);
            // make 0 knowledge
            lr.push((l, r));

            let x_inv_bits = sponge.squeeze_bits(128);
            let x_inv = endoscalar_to_field::<P>(&x_inv_bits[..]);
            let x = x_inv.inverse().unwrap();

            x_invs.push(x_inv);

            blinder += x * l_blinder + x_inv * r_blinder;

            for i in 0..m {
                a[i] = a[i] + x * a[m + i];
                public[i] = public[i] + x_inv * public[m + i];
            }

            a.truncate(m);
            public.truncate(m);

            h = affine_window_combine_one_endo(P::ENDO_COEFFS[0], &h[..m], &h[m..], &x_inv_bits);
        }

        ProverOutput {
            h0: h[0],
            a0: a[0],
            public0: public[0],
            lr,
            blinder,
        }
    }
}

pub struct VerifierOutput<P: SWCurveConfig> {
    pub h0: Projective<P>,
    pub lr_sum: Projective<P>,
    pub public0: P::ScalarField,
}

fn endoscalar_to_field<P: GLVConfig>(r: &[bool]) -> P::ScalarField {
    let mut a: P::ScalarField = 2_u64.into();
    let mut b: P::ScalarField = 2_u64.into();

    let one: P::ScalarField = 1.into();
    let neg_one = -one;

    for i in (0..(r.len() / 2)).rev() {
        a.double_in_place();
        b.double_in_place();

        let r_2i = r[2 * i];
        let s = if !r_2i { &neg_one } else { &one };

        if !r[2 * i + 1] {
            b += s;
        } else {
            a += s;
        }
    }

    a * P::LAMBDA + b
}

fn commitment_key_scalars<F: Field>(chals: &[F]) -> Vec<F> {
    let rounds = chals.len();
    let s_length = 1 << rounds;
    let mut s = vec![F::one(); s_length];
    let mut k: usize = 0;
    let mut pow: usize = 1;
    for i in 1..s_length {
        k += if i == pow { 1 } else { 0 };
        pow <<= if i == pow { 1 } else { 0 };
        s[i] = s[i - (pow >> 1)] * chals[rounds - 1 - (k - 1)];
    }
    s
}

pub fn verify<P: GLVConfig, S: CryptographicSponge>(
    h: &[Affine<P>],
    sponge: &mut S,
    mut public: Vec<P::ScalarField>,
    lr: &[(Affine<P>, Affine<P>)],
) -> VerifierOutput<P> {
    let mut bases = vec![];
    let mut scalars = vec![];
    let mut chals = vec![];

    let ceil_pow2 = 1 << log2(public.len());
    assert!(h.len() >= ceil_pow2);
    let padding = (1 << log2(public.len())) as usize - public.len();
    public.extend((0..padding).map(|_| P::ScalarField::zero()));

    for (l, r) in lr.iter() {
        let m = public.len() / 2;

        absorb_curve(sponge, l);
        absorb_curve(sponge, r);

        let x_inv_bits = sponge.squeeze_bits(128);
        let x_inv = endoscalar_to_field::<P>(&x_inv_bits[..]);
        let x = x_inv.inverse().unwrap();

        chals.push(x_inv);

        for i in 0..m {
            public[i] = public[i] + x_inv * public[m + i];
        }
        public.truncate(m);

        bases.push(*l);
        scalars.push(x);
        bases.push(*r);
        scalars.push(x_inv);
    }

    let public0 = public[0];

    let ck_scalars = commitment_key_scalars(&chals);
    VerifierOutput {
        lr_sum: <Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap(),
        h0: VariableBaseMSM::msm(&h[..ck_scalars.len()], &ck_scalars).unwrap(),
        public0,
    }
}

fn inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    a.iter().zip(b.iter()).map(|(x, y)| *x * y).sum()
}

// TODO: Replace with nice group map
pub fn random_group_element<P: SWCurveConfig>(prefix: &[u8], i: u64) -> Affine<P> {
    let mut j: u32 = 0;
    loop {
        let mut hash = [0u8; 32];
        let mut sponge = Shake::v256();
        sponge.update(prefix);
        sponge.update(&i.to_le_bytes());
        sponge.update(&j.to_le_bytes());
        sponge.finalize(&mut hash);

        let x = P::BaseField::from_random_bytes(&hash);
        match x.and_then(|x| Affine::<P>::get_point_from_x_unchecked(x, false)) {
            None => j += 1,
            Some(p) => return p,
        }
    }
}
