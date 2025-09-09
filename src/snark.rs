// Commit to the limbs,
//
// R_j = r_j G
// C_{i, j} = m_{i, j} G + r_j Y_i
// Commit to the bits with bases H_k, B_{i, j} = \sum m_(i, j, k) H_k
//
// Fiat--Shamir challenges alpha, beta, \delta
//
// Y +: \sum_i \alpha^i Y_i
//
// C = \sum_{i, j} \alpha^i \beta^j C_{i, j}
// = (\sum_{i, j} \alpha^i \beta^j m_{i, j}) G + \sum_{i,j} \alpha^i \beta^j Y_i
// = (\sum_{i, j} \alpha^i \beta^j m_{i, j}) G + \sum_j \sum_i \alpha^i \beta^j Y_i
// = (\sum_{i, j} \alpha^i \beta^j m_{i, j}) G + (\sum_j \beta^j r_j) Y
//
// D = C - \delta \sum_j \beta^j R_j
// = (\sum_{i, j} \alpha^i \beta^j m_{i, j}) G + (\sum_j \beta^j r_j) Y - sum_j \beta^j R_j
// = (\sum_{i, j} \alpha^i \beta^j m_{i, j}) G + (\sum_j \beta^j r_j) Y - (sum_j \beta^j r_j) \delta G
// = (\sum_{i, j} \alpha^i \beta^j m_{i, j}) G + (\sum_j \beta^j r_j) (Y - \delta G)
//
// Prove knowledge of a and b such that D = a G + b (Y - \delta G)
//
// Proves that these are encrypted values.
//
// Need to show the m_{i, j} are small. This we do with bulletproofs.
//
// \sum_{i,j} \alpha^i \beta^j B_{i, j}
// Inner product proof with pows(2) vector
// \sum_{i,j} \gamma^{num(i,j)} C_{i,j}
//
// Combine the Bij into a single column and do a polynomial division check to show bits and an
// inner product to link with the limbs

use core::num;
use std::time::Instant;

use ark_crypto_primitives::sponge::{self, CryptographicSponge};
use ark_ec::{
    AffineRepr, CurveGroup, ScalarMul, VariableBaseMSM,
    scalar_mul::{BatchMulPreprocessing, glv::GLVConfig},
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, BigInteger, Field, One, PrimeField, UniformRand, Zero};
use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{log2, rand::RngCore};
use array_init::array_init;
use itertools::{Itertools, assert_equal};
use rand::random;
use rayon::{array, prelude::*};
use sha2::digest::{generic_array::arr, typenum::bit};
use tiny_keccak::{Hasher, Shake};

use crate::{
    combine::{
        affine_window_combine_one_endo, batch_add_assign_no_branch, batch_glv_mul,
        batch_negate_in_place,
    },
    dlog_table::DLogTable,
    ipa::{self, endoscalar_to_field, pows},
    sponge::ShakeSponge,
};

const LIMBS: usize = 16;
const LIMB_SIZE: usize = 256 / 16;
const BYTES_PER_LIMB: usize = LIMB_SIZE / 8;
const SECRETS: usize = 2;

pub struct Shares<F> {
    pub per_party: Vec<[F; 2]>,
}

pub struct ShareLimbs {
    // By party, then by limb, then by row
    per_party: Vec<[[u16; 2]; LIMBS]>,
}

// 1, ... num_parties
// 1+num_parties, ..., num_parties + num_parties,
fn evaluation_points<F: PrimeField>(num_parties: usize) -> Vec<[F; 2]> {
    (0..num_parties)
        .map(|i| {
            [
                F::from_bigint(((1 + i) as u64).into()).unwrap(),
                F::from_bigint(((1 + num_parties + i) as u64).into()).unwrap(),
            ]
        })
        .collect()
}

impl<F: PrimeField> Shares<F> {
    pub fn to_limbs(&self) -> ShareLimbs {
        let per_party: Vec<[[u16; 2]; LIMBS]> = self
            .per_party
            .iter()
            .map(|shares| {
                let mut by_limb = [[0u16; SECRETS]; LIMBS];
                for k in 0..SECRETS {
                    let bytes = shares[k].into_bigint().to_bytes_le();
                    for (j, cs) in bytes.chunks(BYTES_PER_LIMB).enumerate() {
                        assert_eq!(cs.len(), BYTES_PER_LIMB);
                        by_limb[j][k] = (cs[0] as u16) + ((cs[1] as u16) << 8);
                    }
                }
                by_limb
            })
            .collect();
        ShareLimbs { per_party }
    }

    pub fn create<R: RngCore>(rng: &mut R, num_parties: usize, threshold: usize) -> Self {
        let mut per_party: Vec<[F; 2]> = vec![[F::zero(); 2]; num_parties];
        let pts = evaluation_points::<F>(num_parties);

        for k in 0..SECRETS {
            let mut p = DensePolynomial::<F>::rand(threshold - 1, rng);
            p.coeffs[0] = F::zero();

            for i in 0..num_parties {
                per_party[i][k] = p.evaluate(&pts[i][k])
            }
        }
        Shares { per_party }
    }
}

pub struct EncryptedShares<P: SWCurveConfig> {
    // By limb, then by row
    pub randomness: [[Affine<P>; 2]; LIMBS],
    // By party, then by limb, then by row
    pub per_party: Vec<[[Affine<P>; 2]; LIMBS]>,
}

pub struct SinglePartyEncryptedShares<'a, G> {
    // By limb, then by row
    pub randomness: &'a [[G; 2]; LIMBS],
    // By limb, then by row
    pub by_limb: &'a [[G; 2]; LIMBS],
}

struct InputColumns<C> {
    // First by party, then by limb
    by_party: Vec<[C; LIMBS]>,
}

struct ProofColumns<C> {
    lookup_accumulator: Vec<C>,
    lookup_counts: C,
}

struct Proof<P: SWCurveConfig> {
    bit_packing: BitpackingIPA<P>,
}

pub struct EncryptedSharesWithProof<P: SWCurveConfig> {
    shares: EncryptedShares<P>,
    proof: Proof<P>,
}

impl<P: GLVConfig> EncryptedSharesWithProof<P> {
    pub fn decrypt_and_verify(
        &self,
        encryption_params: &EncryptionParams<Affine<P>>,
        bitpacking_ipa_params: &BitPackingIPAParams<P>,
        table: &DLogTable<P>,
        secret_key: P::ScalarField,
        i: usize,
        public_keys: &Vec<Affine<P>>,
    ) -> Option<[P::ScalarField; 2]> {
        if self.verify(encryption_params, bitpacking_ipa_params, public_keys) {
            let shares: SinglePartyEncryptedShares<Affine<P>> = SinglePartyEncryptedShares {
                by_limb: &self.shares.per_party[i],
                randomness: &self.shares.randomness,
            };

            Some(decrypt(shares, table, secret_key))
        } else {
            None
        }
    }

    pub fn verify(
        &self,
        encryption_params: &EncryptionParams<Affine<P>>,
        bitpacking_ipa_params: &BitPackingIPAParams<P>,
        public_keys: &Vec<Affine<P>>,
    ) -> bool {
        let mut sponge = ShakeSponge::new(&());

        bitpacking_ipa_params.verify(
            encryption_params,
            &mut sponge,
            &self.shares,
            public_keys,
            &self.proof.bit_packing,
        )
    }
}

fn map<A: Copy, C, F: Fn(A) -> C, const N: usize>(xs: &[A; N], f: F) -> [C; N] {
    array_init(|i| f(xs[i]))
}

fn map2<A: Copy, B: Copy, C, F: Fn(A, B) -> C, const N: usize>(
    xs: &[A; N],
    ys: &[B; N],
    f: F,
) -> [C; N] {
    array_init(|i| f(xs[i], ys[i]))
}

struct BitpackingIPAChallenges<P: SWCurveConfig> {
    alpha: P::ScalarField,
    beta: P::ScalarField,
    gamma: P::ScalarField,
    delta: P::ScalarField,
}

impl<P: SWCurveConfig> BitpackingIPAChallenges<P> {
    fn combined_public_key(&self, public_keys: &Vec<Affine<P>>) -> Projective<P> {
        <Projective<P> as VariableBaseMSM>::msm(
            public_keys,
            &pows(self.alpha).take(public_keys.len()).collect_vec(),
        )
        .unwrap()
    }

    fn bit_packing_coefficients(&self, num_parties: usize) -> Vec<P::ScalarField> {
        let BitpackingIPAChallenges {
            alpha,
            beta,
            gamma,
            delta: _,
        } = &self;

        let mut public = vec![];
        let mut alpha_i = P::ScalarField::one();
        for _i in 0..num_parties {
            let mut alpha_i_beta_j = alpha_i;
            for _j in 0..LIMBS {
                let mut alpha_i_beta_j_gamma_k = alpha_i_beta_j;
                for _k in 0..2 {
                    // 2^l * alpha^i * beta^j * gamma^k
                    let mut c = alpha_i_beta_j_gamma_k;
                    for _l in 0..LIMB_SIZE {
                        public.push(c);
                        c.double_in_place();
                    }
                    alpha_i_beta_j_gamma_k *= gamma;
                }
                alpha_i_beta_j *= beta;
            }
            alpha_i *= alpha;
        }

        // pad
        /*
                let padding = (1 << log2(public.len()) as usize) - public.len();
                public.extend((0..padding).map(|_| P::ScalarField::zero()));
        */
        public
    }
}

impl<P: GLVConfig> EncryptedShares<P> {
    fn challenges<S: CryptographicSponge>(&self, sponge: &mut S) -> BitpackingIPAChallenges<P> {
        self.randomness
            .iter()
            .for_each(|rs| rs.iter().for_each(|r| absorb_curve(sponge, r)));
        self.per_party.iter().for_each(|p| {
            p.iter()
                .for_each(|ss| ss.iter().for_each(|s| absorb_curve(sponge, s)))
        });
        let x = sponge.squeeze_field_elements::<P::ScalarField>(4);
        BitpackingIPAChallenges {
            alpha: x[0],
            beta: x[1],
            gamma: x[2],
            delta: x[3],
        }
    }

    // \delta \sum_jk \beta^j \gamma^k R_jk + sum_ijk \alpha^i \beta^j \gamma^k C_ijk
    fn combined_commitment(&self, chals: &BitpackingIPAChallenges<P>) -> Projective<P> {
        let BitpackingIPAChallenges {
            alpha,
            beta,
            gamma,
            delta,
        } = chals;

        let mut bases = vec![];
        let mut scalars = vec![];
        let mut alpha_i = P::ScalarField::one();

        for (i, p) in self.per_party.iter().enumerate() {
            let mut alpha_i_beta_j = alpha_i;
            for j in 0..self.randomness.len() {
                let ss = p[j];
                let rs = self.randomness[j];
                let mut alpha_i_beta_j_gamma_k = alpha_i_beta_j;
                for k in 0..ss.len() {
                    // only add in the randomness once, when alpha^i = 1
                    if i == 0 {
                        bases.push(rs[k]);
                        scalars.push(alpha_i_beta_j_gamma_k * delta);
                    }
                    bases.push(ss[k]);
                    scalars.push(alpha_i_beta_j_gamma_k);

                    alpha_i_beta_j_gamma_k *= gamma;
                }
                alpha_i_beta_j *= beta;
            }
            alpha_i *= alpha;
        }
        <Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
    }
}

pub fn decrypt<P: SWCurveConfig + GLVConfig>(
    shares: SinglePartyEncryptedShares<Affine<P>>,
    table: &DLogTable<P>,
    secret_key: P::ScalarField,
    //    z: P::ScalarField,
) -> [P::ScalarField; 2] {
    let num_secrets = shares.by_limb[0].len();
    // let mut zs = pows(z).take(num_secrets).collect_vec();
    // batch_inversion(&mut zs);
    // let zinvs = zs;

    let limbs: Vec<Vec<u16>> = shares
        .by_limb
        .iter()
        .zip(shares.randomness.iter())
        .map(|(cs, rs)| {
            let mut yrs = batch_glv_mul(rs, secret_key);
            batch_negate_in_place(&mut yrs);
            let mut denoms = vec![P::BaseField::zero(); num_secrets];
            batch_add_assign_no_branch(&mut denoms, &mut yrs, cs);
            let res = yrs;
            res.par_iter()
                .map(|g| table.bruteforce_dlog(g).unwrap())
                .collect()
        })
        .collect();

    array_init::array_init(|i| {
        // limbs.iter().map(|limb| limb[i]).concat!
        let mut bytes = vec![];
        for limb in limbs.iter() {
            let x = limb[i];
            bytes.push(x as u8);
            bytes.push((x >> 8) as u8);
        }
        <P::ScalarField as PrimeField>::from_le_bytes_mod_order(&bytes[..])
    })
}

pub fn encrypt<R: RngCore, P: GLVConfig + SWCurveConfig>(
    params: &EncryptionParams<Affine<P>>,
    bitpacking_ipa_params: &BitPackingIPAParams<P>,
    // The table is a table of powers of ipa_params.inner_product_base
    table: &DLogTable<P>,
    limbs: &ShareLimbs,
    public_keys: &Vec<Affine<P>>,
    rng: &mut R,
) -> EncryptedSharesWithProof<P> {
    let num_limbs = limbs.per_party[0].len();
    println!("{num_limbs}");
    let num_secrets = limbs.per_party[0][0].len();
    println!("start rand");
    let rs: [[P::ScalarField; 2]; LIMBS] =
        array_init(|_j| array_init(|_k| P::ScalarField::rand(rng)));
    let randomness: [[_; 2]; LIMBS] = map(&rs, |v| {
        let res: Vec<Projective<_>> = v
            .par_iter()
            .map(|x| GLVConfig::glv_mul_projective(params.public_key_base.into_group(), *x))
            .collect();
        let res = Projective::<P>::normalize_batch(&res);
        array_init(|i| res[i])
    });

    let shares: Vec<_> = limbs
        .per_party
        .iter()
        .zip(public_keys.iter())
        .map(|(by_limb, pk)| {
            let pk_table = BatchMulPreprocessing::new(pk.into_group(), num_secrets);
            map2(by_limb, &rs, |v, r| {
                let res = v.map(|m| table.from_u16(m));
                let pkr = pk_table.batch_mul(&r);
                array_init::array_init(|i| (res[i] + pkr[i]).into_affine())
            })
        })
        .collect();

    let encrypted_shares = EncryptedShares {
        randomness,
        per_party: shares,
    };

    let mut sponge = ShakeSponge::new(&());
    let (_bitpacking_chals, bitpacking_ipa) = bitpacking_ipa_params.prove(
        limbs,
        &rs,
        &encrypted_shares,
        &params,
        public_keys,
        &mut sponge,
        rng,
    );

    EncryptedSharesWithProof {
        shares: encrypted_shares,
        proof: Proof {
            bit_packing: bitpacking_ipa,
        },
    }
}

pub struct EncryptionParams<G> {
    pub public_key_base: G,
}

pub struct BitpackingIPA<P: SWCurveConfig> {
    bit_commitment: Affine<P>,
    lr: Vec<(Affine<P>, Affine<P>)>,
    schnorr: Schnorr<3, P>,
}

pub struct IPAParams<P: SWCurveConfig> {
    h: Vec<Affine<P>>,
    blinder_base: Affine<P>,
    // Has to be the same as the encryption base
    pub inner_product_base: Affine<P>,
}

pub struct BitPackingIPAParams<P: SWCurveConfig> {
    pub ipa: IPAParams<P>,
    num_parties: usize,
}

pub struct PolynomialCommitmentIPAParams<P: SWCurveConfig> {
    ipa: IPAParams<P>,
}

pub struct PolynomialCommitmentIPA<G> {
    lr: Vec<(G, G)>,
    schnorr: (),
}

pub struct Schnorr<const N: usize, P: SWCurveConfig> {
    z: [P::ScalarField; N],
    rg: Affine<P>,
}

impl<const N: usize, P: SWCurveConfig> Schnorr<N, P> {
    fn verify<S: CryptographicSponge>(
        &self,
        comm: Projective<P>,
        g: &[Affine<P>],
        sponge: &mut S,
    ) -> bool {
        absorb_curve(sponge, &self.rg);
        let c = sponge.squeeze_field_elements::<P::ScalarField>(1)[0];
        let zg = <Projective<P> as VariableBaseMSM>::msm(&g, &self.z).unwrap();
        comm * c + self.rg == zg
    }

    fn prove<R: RngCore, S: CryptographicSponge>(
        g: &[Affine<P>],
        s: &[P::ScalarField],
        sponge: &mut S,
        rng: &mut R,
    ) -> Self {
        let r: [_; N] = array_init(|_| P::ScalarField::rand(rng));
        let rg = <Projective<P> as VariableBaseMSM>::msm(&g, &r)
            .unwrap()
            .into_affine();
        absorb_curve(sponge, &rg);
        let c = sponge.squeeze_field_elements::<P::ScalarField>(1)[0];
        let z = array_init(|i| c * s[i] + r[i]);
        Self { rg, z }
    }
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

impl<P: SWCurveConfig + GLVConfig> IPAParams<P> {
    pub fn new(prefix: &[u8], n: usize) -> Self {
        let n = n as u64;
        let h = (0..n).map(|i| random_group_element(prefix, i)).collect();
        let blinder_base = random_group_element(prefix, n);
        let inner_product_base = random_group_element(prefix, n + 1);
        IPAParams {
            h,
            blinder_base,
            inner_product_base,
        }
    }
}

impl<P: GLVConfig> BitPackingIPAParams<P> {
    pub fn new(num_parties: usize) -> Self {
        let prefix = b"bit_packing_ipa_param";
        let num_bits = 1 << log2(num_parties * SECRETS * LIMBS * LIMB_SIZE);
        BitPackingIPAParams {
            ipa: IPAParams::new(prefix, num_bits),
            num_parties,
        }
    }

    fn schnorr_bases(
        h0: Affine<P>,
        public0: P::ScalarField,
        inner_product_base: Affine<P>,
        delta: P::ScalarField,
        y: Affine<P>,
        public_key_base: Affine<P>,
        blinder_base: Affine<P>,
    ) -> [Affine<P>; 3] {
        [
            (h0 + inner_product_base * public0).into_affine(),
            (y + (public_key_base * delta)).into_affine(),
            blinder_base,
        ]
    }

    pub fn prove<R: RngCore, S: CryptographicSponge>(
        &self,
        shares: &ShareLimbs,
        encryption_randomness: &[[P::ScalarField; 2]; LIMBS],
        encrypted_shares: &EncryptedShares<P>,
        encryption_params: &EncryptionParams<Affine<P>>,
        public_keys: &Vec<Affine<P>>,
        sponge: &mut S,
        rng: &mut R,
    ) -> (BitpackingIPAChallenges<P>, BitpackingIPA<P>) {
        let mut bits: Vec<P::ScalarField> = vec![];
        let bit_commitment_blinder = P::ScalarField::rand(rng);
        // TODO: Use a batch affine version if efficiency is needed.
        let mut bit_commitment = self.ipa.blinder_base * bit_commitment_blinder;
        let mut idx = 0;
        for i in 0..self.num_parties {
            for j in 0..LIMBS {
                for k in 0..2 {
                    for l in 0..LIMB_SIZE {
                        let b = (shares.per_party[i][j][k] >> l) & 1;
                        if b == 1 {
                            bit_commitment += self.ipa.h[idx];
                        }
                        bits.push(P::ScalarField::from_bigint(b.into()).unwrap());
                        idx += 1;
                    }
                }
            }
        }
        let bit_commitment = bit_commitment.into_affine();
        absorb_curve(sponge, &bit_commitment);
        let chals = encrypted_shares.challenges(sponge);

        // sum_jk beta^j gamma^k r_jk
        let r = {
            let mut r = P::ScalarField::zero();
            let mut beta_j = P::ScalarField::one();
            for j in 0..LIMBS {
                let mut beta_j_gamma_k = beta_j;
                for k in 0..2 {
                    r += beta_j_gamma_k * encryption_randomness[j][k];
                    beta_j_gamma_k *= chals.gamma;
                }
                beta_j *= chals.beta;
            }
            r
        };

        let ipa = self.ipa.prove(
            sponge,
            rng,
            bits,
            chals.bit_packing_coefficients(self.num_parties),
        );

        println!("P alpha {:?}", chals.alpha);
        println!("P h0 {:?}", ipa.h0);
        println!("P public0 {:?}", ipa.public0);
        let schnorr_bases = BitPackingIPAParams::schnorr_bases(
            ipa.h0,
            ipa.public0,
            self.ipa.inner_product_base,
            chals.delta,
            chals.combined_public_key(public_keys).into_affine(),
            encryption_params.public_key_base,
            self.ipa.blinder_base,
        );
        println!("P schnorr bases {schnorr_bases:?}");
        let schnorr = Schnorr::prove(
            &schnorr_bases,
            &[ipa.a0, r, bit_commitment_blinder + ipa.blinder],
            sponge,
            rng,
        );

        (
            chals,
            BitpackingIPA {
                bit_commitment,
                lr: ipa.lr,
                schnorr,
            },
        )
    }

    pub fn verify<S: CryptographicSponge>(
        &self,
        encryption_params: &EncryptionParams<Affine<P>>,
        sponge: &mut S,
        encrypted_shares: &EncryptedShares<P>,
        public_keys: &Vec<Affine<P>>,
        // chals: &BitpackingIPAChallenges<P>,
        // c_0: Projective<P>,
        proof: &BitpackingIPA<P>,
    ) -> bool {
        absorb_curve(sponge, &proof.bit_commitment);

        let chals = encrypted_shares.challenges(sponge);
        let c_0 = encrypted_shares.combined_commitment(&chals) + proof.bit_commitment;

        let public = chals.bit_packing_coefficients(self.num_parties);

        let IPAVerifierOutput {
            h0,
            public0,
            lr_sum,
        } = verify_ipa(&self.ipa.h, sponge, public, &proof.lr);

        // Check lr_sum + c_0 == ()
        // Need to verify knowledge of a, s, t  such that
        //
        // C_0 + lr_sum
        // = (a * (h0 + public0 * inner_product_base)) + t (Y + \delta G) + s * blinder_base

        println!("V alpha {:?}", chals.alpha);
        println!("V h0 {:?}", h0.into_affine());
        println!("V public0 {:?}", public0);

        let schnorr_bases = BitPackingIPAParams::schnorr_bases(
            h0.into_affine(),
            public0,
            self.ipa.inner_product_base,
            chals.delta,
            chals.combined_public_key(public_keys).into_affine(),
            encryption_params.public_key_base,
            self.ipa.blinder_base,
        );
        println!("V schnorr bases {schnorr_bases:?}");
        proof.schnorr.verify(c_0 + lr_sum, &schnorr_bases, sponge)
    }
}

fn absorb_curve<P: SWCurveConfig, S: CryptographicSponge>(sponge: &mut S, g: &Affine<P>) {
    let (x, y) = g.xy().unwrap();
    let mut buf = vec![0; P::BaseField::uncompressed_size(&x)];
    x.serialize_uncompressed(&mut buf).ok();
    sponge.absorb(&buf);
    buf.iter_mut().for_each(|x| *x = 0);
    y.serialize_uncompressed(&mut buf).ok();
    sponge.absorb(&buf);
}

fn inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    a.iter().zip(b.iter()).map(|(x, y)| *x * y).sum()
}

struct IPAProverOutput<P: SWCurveConfig> {
    lr: Vec<(Affine<P>, Affine<P>)>,
    h0: Affine<P>,
    a0: P::ScalarField,
    public0: P::ScalarField,
    blinder: P::ScalarField,
}

struct IPAVerifierOutput<P: SWCurveConfig> {
    h0: Projective<P>,
    lr_sum: Projective<P>,
    public0: P::ScalarField,
}

pub fn verify_ipa<P: GLVConfig, S: CryptographicSponge>(
    h: &Vec<Affine<P>>,
    sponge: &mut S,
    mut public: Vec<P::ScalarField>,
    lr: &Vec<(Affine<P>, Affine<P>)>,
) -> IPAVerifierOutput<P> {
    let mut bases = vec![];
    let mut scalars = vec![];
    let mut chals = vec![];
    let mut idx = 0;

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

        println!("V m {m}");
        println!("V public0 {idx} = {:?}", public[0]);
        println!("V publicm {idx} = {:?}", public[m]);
        for i in 0..m {
            public[i] = public[i] + x_inv * public[m + i];
        }
        public.truncate(m);

        bases.push(*l);
        scalars.push(x);
        bases.push(*r);
        scalars.push(x_inv);
        idx += 1;
    }

    let public0 = public[0];

    IPAVerifierOutput {
        lr_sum: <Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap(),
        h0: VariableBaseMSM::msm_unchecked(h, &commitment_key_scalars(&chals)),
        public0,
    }
}

impl<P: GLVConfig> IPAParams<P> {
    fn prove<R: RngCore, S: CryptographicSponge>(
        &self,
        sponge: &mut S,
        rng: &mut R,
        mut a: Vec<P::ScalarField>,
        mut public: Vec<P::ScalarField>,
    ) -> IPAProverOutput<P> {
        let mut blinder = P::ScalarField::zero();
        let mut lr = vec![];

        // pad
        assert_eq!(a.len(), public.len());
        let ceil_pow2 = 1 << log2(a.len());
        assert!(self.h.len() >= ceil_pow2);
        let mut h = self.h[..ceil_pow2].to_vec();
        let padding = (1 << log2(a.len())) as usize - a.len();
        a.extend((0..padding).map(|_| P::ScalarField::zero()));
        public.extend((0..padding).map(|_| P::ScalarField::zero()));

        let mut idx = 0;
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

            blinder += x * l_blinder + x_inv * r_blinder;

            println!("P m {m}");
            println!("P public0 {idx} = {:?}", public[0]);
            println!("P publicm {idx} = {:?}", public[m]);
            for i in 0..m {
                a[i] = a[i] + x * a[m + i];
                public[i] = public[i] + x_inv * public[m + i];
            }

            a.truncate(m);
            public.truncate(m);

            h = affine_window_combine_one_endo(P::ENDO_COEFFS[0], &h[..m], &h[m..], &x_inv_bits);
            idx += 1;
        }

        IPAProverOutput {
            h0: h[0],
            a0: a[0],
            public0: public[0],
            lr,
            blinder,
        }
    }
}

pub fn prove_ipa<P: GLVConfig, R: RngCore, S: CryptographicSponge>(
    blinder_base: Affine<P>,
    inner_product_base: Affine<P>,
    mut h: Vec<Affine<P>>,
    rng: &mut R,
    sponge: &mut S,
    mut a: Vec<P::ScalarField>,
    mut public: Vec<P::ScalarField>,
    // The main commitment
    /*
        c_0: Affine<P>,
        y_minus_delta_g: Affine<P>,
        y_minus_delta_g_coeff: P::ScalarField,
    */
) -> IPAProverOutput<P> {
    let mut blinder = P::ScalarField::zero();
    let mut lr = vec![];

    // pad
    assert_eq!(a.len(), public.len());
    let padding = (1 << log2(a.len())) as usize - a.len();
    a.extend((0..padding).map(|_| P::ScalarField::zero()));
    public.extend((0..padding).map(|_| P::ScalarField::zero()));

    while a.len() > 1 {
        let m = a.len() / 2;
        let l_blinder = P::ScalarField::rand(rng);
        let r_blinder = P::ScalarField::rand(rng);
        let z_l = inner_product(&a[m..], &public[..m]);
        let z_r = inner_product(&a[..m], &public[m..]);

        let l = <Projective<P> as VariableBaseMSM>::msm(&h[..m], &a[m..]).unwrap()
            + blinder_base * l_blinder
            + inner_product_base * z_l;
        let r = <Projective<P> as VariableBaseMSM>::msm(&h[m..], &a[..m]).unwrap()
            + blinder_base * r_blinder
            + inner_product_base * z_r;
        let l = l.into_affine();
        let r = r.into_affine();
        absorb_curve(sponge, &l);
        absorb_curve(sponge, &r);
        // make 0 knowledge
        lr.push((l, r));

        let x_inv_bits = sponge.squeeze_bits(128);
        let x_inv = endoscalar_to_field::<P>(&x_inv_bits[..]);
        let x = x_inv.inverse().unwrap();

        blinder += x * l_blinder + x_inv * r_blinder;

        for i in 0..m {
            a[i] = a[i] + x * a[m + i];
            public[i] = public[i] + x_inv * public[m + i];
        }
        a.truncate(m);
        public.truncate(m);

        h = affine_window_combine_one_endo(P::ENDO_COEFFS[0], &h[..m], &h[m..], &x_inv_bits);
    }

    return IPAProverOutput {
        h0: h[0],
        a0: a[0],
        public0: public[0],
        lr,
        blinder,
    };

    // Let C_0 be our original commitment.
    // Let C = a[0] * (h[0] + public[0] inner_product_base)
    // At the end, we want to prove knowledge of a, s, t  such that
    //
    // C_0 + \sum x_i l_i + x_inv_i r_i
    // = (a * (h[0] + public[0] * inner_product_base)) + t (Y - \delta G) + s * blinder_base
    let r_a = P::ScalarField::rand(rng);
    /*
    let r_s = P::ScalarField::rand(rng);
    let r_t = P::ScalarField::rand(rng);

        let c = <Projective<P> as VariableBaseMSM>::msm(
            &[h[0], inner_product_base, blinder_base, y_minus_delta_g],
            &[a[0], a[0] * public[0], blinder, y_minus_delta_g_coeff],
        )
        .unwrap()
        .into_affine();
    */
    // TODO:schnorr
}
