use std::os::macos::raw::stat;

use crate::combine::affine_window_combine_one_endo;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::{
    AffineRepr, CurveGroup, VariableBaseMSM,
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine as SWAffine, Projective as SWProjective, SWCurveConfig},
    twisted_edwards::Projective,
};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField, UniformRand, Zero};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;

pub struct CommitmentKey<P: SWCurveConfig> {
    pub g: Vec<SWAffine<P>>,
    pub h: Vec<SWAffine<P>>,
    pub blinder: SWAffine<P>,
}

#[derive(Debug, Clone, Copy)]
pub struct Commitment<G>(pub G, pub G);

#[derive(Debug, Clone)]
pub struct MsmProof<F, G> {
    lr: Vec<(Commitment<G>, Commitment<G>)>,
    a: F,
    schnorr: Commitment<(G, F)>,
}

// This is a specific MSM proof that we use in the non-interactive secret sharing protocol.
// Specifically, given public inputs
// u: Group
// c: Group
// y: Group
// gamma, delta: ScalarField
// and lagrange commitments L_0, ... L_{m-1},
// we prove
// there exists a such that
// < h, a > = u
// and
// < V, a > = c
// where V = (gamma^0 y + delta^0 g, ..., gamma^{m-1} y + delta^{m-1} g, gamma^0 L_0, gamma^{m-1} L_{m-1})
//
// We specialize the inner-product argument from the general MSM one so that we can avoid computing
// the elements of V explicitly in the verifier, since it is costly to do so.
pub struct DlogProofCommitmentKey<P: SWCurveConfig> {
    h: Vec<SWAffine<P>>,
    g: SWAffine<P>,
    blinder: SWAffine<P>,
}

type LRCommitments<P> = Vec<(Commitment<SWAffine<P>>, Commitment<SWAffine<P>>)>;

fn process_lr<S: CryptographicSponge, P: SWCurveConfig + GLVConfig>(
    sponge: &mut S,
    lr: &LRCommitments<P>,
    Commitment(c1, c2): Commitment<SWAffine<P>>,
) -> (Vec<P::ScalarField>, Commitment<SWProjective<P>>) {
    let mut c1 = c1.into_group();
    let mut c2 = c2.into_group();

    let mut chal_invs = vec![];
    for (Commitment(l1, l2), Commitment(r1, r2)) in lr.iter() {
        absorb_curve(sponge, *l1);
        absorb_curve(sponge, *l2);
        absorb_curve(sponge, *r1);
        absorb_curve(sponge, *r2);

        let x_inv = sponge.squeeze_bits(128);
        let x_inv_field = endoscalar_to_field::<P>(&x_inv[..]);
        let x = x_inv_field.inverse().unwrap();
        chal_invs.push(x_inv_field);

        c1 += *l1 * x;
        c1 += *r1 * x_inv_field;
        c2 += *l2 * x;
        c2 += *r2 * x_inv_field;
    }

    (chal_invs, Commitment(c1, c2))
}

impl<P: SWCurveConfig + GLVConfig> DlogProofCommitmentKey<P> {
    pub fn verify<S: CryptographicSponge>(
        &self,
        lagrange: &[SWAffine<P>],
        statement: &DlogProofStatement<P::ScalarField, SWAffine<P>>,
        sponge: &mut S,
        proof: &MsmProof<P::ScalarField, SWAffine<P>>,
        comm: Commitment<SWAffine<P>>,
    ) -> bool {
        let (chal_invs, Commitment(c1, c2)) = process_lr(sponge, &proof.lr, comm);
        let ss = commitment_key_scalars(&chal_invs);

        let m = ss.len() / 2;

        let g_scalar = ss[..m]
            .iter()
            .zip(pows(statement.delta))
            .map(|(s, d)| *s * d)
            .sum();
        let y_scalar = ss[..m]
            .iter()
            .zip(pows(statement.gamma))
            .map(|(s, d)| *s * d)
            .sum();
        let mut scalars: Vec<_> = ss[m..]
            .iter()
            .zip(pows(statement.gamma))
            .map(|(s, d)| *s * d)
            .collect();

        let mut bases = lagrange.to_vec();
        bases.push(self.g);
        scalars.push(g_scalar);
        bases.push(statement.y);
        scalars.push(y_scalar);

        let g0 = <SWProjective<P> as VariableBaseMSM>::msm(&bases[..], &scalars[..])
            .unwrap()
            .into_affine();
        let h0 = <SWProjective<P> as VariableBaseMSM>::msm(&self.h[..], &ss[..])
            .unwrap()
            .into_affine();

        // basically checking
        // g0 * proof.a == c1 && h0 * proof.a == c2
        // instead checking that
        // c1 - g0 * proof.a is a multiple of self.blinder
        // AND c2 - h0 * proof.a is a multiple of self.blinder

        let Commitment((u1, z1), (u2, z2)) = proof.schnorr;

        sponge.absorb(&proof.a.into_bigint().to_bytes_le());
        absorb_curve(sponge, u1);
        absorb_curve(sponge, u2);

        let c: Vec<P::ScalarField> = sponge.squeeze_field_elements(2);

        (c1 - g0 * proof.a) * c[0] + u1 == self.blinder * z1
            && (c2 - h0 * proof.a) * c[1] + u2 == self.blinder * z2
    }
}

pub struct DlogProofStatement<F, G> {
    u: G,
    c: G,
    y: G,
    gamma: F,
    delta: F,
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

fn absorb_curve<P: SWCurveConfig, S: CryptographicSponge>(sponge: &mut S, g: SWAffine<P>) {
    let (x, y) = g.xy().unwrap();
    let mut buf = vec![0; P::BaseField::uncompressed_size(&x)];
    x.serialize_uncompressed(&mut buf).ok();
    sponge.absorb(&buf);
    buf.iter_mut().for_each(|x| *x = 0);
    y.serialize_uncompressed(&mut buf).ok();
    sponge.absorb(&buf);
}

pub fn endoscale<P: GLVConfig>(g: SWAffine<P>, r: &[bool]) -> P::ScalarField {
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
pub fn endoscalar_to_field<P: GLVConfig>(r: &[bool]) -> P::ScalarField {
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

pub struct Pows<F> {
    acc: F,
    base: F,
}

impl<F: Field> Iterator for Pows<F> {
    type Item = F;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.acc;
        self.acc *= self.base;
        Some(res)
    }
}

pub fn pows<F: Field>(x: F) -> Pows<F> {
    Pows {
        acc: F::one(),
        base: x,
    }
}

impl<P: SWCurveConfig + GLVConfig> CommitmentKey<P> {
    pub fn verify<S: CryptographicSponge>(
        &self,
        sponge: &mut S,
        proof: &MsmProof<P::ScalarField, SWAffine<P>>,
        Commitment(c1, c2): Commitment<SWAffine<P>>,
    ) -> bool {
        let mut c1 = c1.into_group();
        let mut c2 = c2.into_group();

        let mut chal_invs = vec![];
        for (Commitment(l1, l2), Commitment(r1, r2)) in proof.lr.iter() {
            absorb_curve(sponge, *l1);
            absorb_curve(sponge, *l2);
            absorb_curve(sponge, *r1);
            absorb_curve(sponge, *r2);

            let x_inv = sponge.squeeze_bits(128);
            let x_inv_field = endoscalar_to_field::<P>(&x_inv[..]);
            let x = x_inv_field.inverse().unwrap();
            chal_invs.push(x_inv_field);

            c1 += *l1 * x;
            c1 += *r1 * x_inv_field;
            c2 += *l2 * x;
            c2 += *r2 * x_inv_field;
        }
        let ss = commitment_key_scalars(&chal_invs);
        let g0 = <SWProjective<P> as VariableBaseMSM>::msm(&self.g[..], &ss[..])
            .unwrap()
            .into_affine();
        let h0 = <SWProjective<P> as VariableBaseMSM>::msm(&self.h[..], &ss[..])
            .unwrap()
            .into_affine();

        // basically checking
        // g0 * proof.a == c1 && h0 * proof.a == c2
        // instead checking that
        // c1 - g0 * proof.a is a multiple of self.blinder
        // AND c2 - h0 * proof.a is a multiple of self.blinder

        let Commitment((u1, z1), (u2, z2)) = proof.schnorr;

        sponge.absorb(&proof.a.into_bigint().to_bytes_le());
        absorb_curve(sponge, u1);
        absorb_curve(sponge, u2);

        let c: Vec<P::ScalarField> = sponge.squeeze_field_elements(2);

        (c1 - g0 * proof.a) * c[0] + u1 == self.blinder * z1
            && (c2 - h0 * proof.a) * c[1] + u2 == self.blinder * z2
    }

    /// Instance:
    /// Commitment C
    /// Prove I know a such that (msm(self.g, a), msm(self.h, a)) == C
    /// TODO: have top level blinder
    pub fn prove<R: RngCore, S: CryptographicSponge>(
        &self,
        rng: &mut R,
        sponge: &mut S,
        mut a: Vec<P::ScalarField>,
    ) -> MsmProof<P::ScalarField, SWAffine<P>> {
        let mut blinder1 = P::ScalarField::zero();
        let mut blinder2 = P::ScalarField::zero();
        let mut lr = vec![];

        let mut g = self.g.clone();
        let mut h = self.h.clone();

        while a.len() > 1 {
            let m = a.len() / 2;
            let l1_blinder = P::ScalarField::rand(rng);
            let l2_blinder = P::ScalarField::rand(rng);
            let r1_blinder = P::ScalarField::rand(rng);
            let r2_blinder = P::ScalarField::rand(rng);
            let l1 = <SWProjective<P> as VariableBaseMSM>::msm(&g[..m], &a[m..]).unwrap()
                + self.blinder * l1_blinder;
            let l2 = <SWProjective<P> as VariableBaseMSM>::msm(&h[..m], &a[m..]).unwrap()
                + self.blinder * l2_blinder;
            let r1 = <SWProjective<P> as VariableBaseMSM>::msm(&g[m..], &a[..m]).unwrap()
                + self.blinder * r1_blinder;
            let r2 = <SWProjective<P> as VariableBaseMSM>::msm(&h[m..], &a[..m]).unwrap()
                + self.blinder * r2_blinder;
            let l1 = l1.into_affine();
            let l2 = l2.into_affine();
            let r1 = r1.into_affine();
            let r2 = r2.into_affine();
            absorb_curve(sponge, l1);
            absorb_curve(sponge, l2);
            absorb_curve(sponge, r1);
            absorb_curve(sponge, r2);
            // make 0 knowledge
            lr.push((Commitment(l1, l2), Commitment(r1, r2)));

            let x_inv = sponge.squeeze_bits(128);
            let x_inv_field = endoscalar_to_field::<P>(&x_inv[..]);
            let x = x_inv_field.inverse().unwrap();

            blinder1 += x * l1_blinder + x_inv_field * r1_blinder;
            blinder2 += x * l2_blinder + x_inv_field * r2_blinder;

            for i in 0..m {
                a[i] = x * a[i] + a[m + i];
            }
            a.truncate(m);

            g = affine_window_combine_one_endo(P::ENDO_COEFFS[0], &g[..m], &g[m..], &x_inv);
            h = affine_window_combine_one_endo(P::ENDO_COEFFS[0], &h[..m], &h[m..], &x_inv);
        }

        // Slap a schnorr proof on it since we made the lr commitments blinded
        let r1 = P::ScalarField::rand(rng);
        let r2 = P::ScalarField::rand(rng);
        let u1 = (self.blinder * r1).into_affine();
        let u2 = (self.blinder * r2).into_affine();
        sponge.absorb(&a[0].into_bigint().to_bytes_le());
        absorb_curve(sponge, u1);
        absorb_curve(sponge, u2);
        let c: Vec<P::ScalarField> = sponge.squeeze_field_elements(2);
        let z1 = r1 + c[0] * blinder1;
        let z2 = r2 + c[1] * blinder2;

        MsmProof {
            lr,
            a: a[0],
            schnorr: Commitment((u1, z1), (u2, z2)),
        }
    }
}
