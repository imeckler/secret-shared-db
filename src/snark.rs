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

use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::{
    AffineRepr, CurveGroup, VariableBaseMSM,
    scalar_mul::{BatchMulPreprocessing, glv::GLVConfig},
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{AdditiveGroup, BigInteger, Field, One, PrimeField, UniformRand, Zero};
use ark_poly::{
    DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
    univariate::DensePolynomial,
};
use ark_std::{iterable::Iterable, log2, rand::RngCore};
use array_init::array_init;
use itertools::Itertools;
use rayon::prelude::*;

use crate::{
    combine::{batch_add_assign_no_branch, batch_glv_mul, batch_negate_in_place},
    dlog_table::DLogTable,
    ipa,
    pows::pows,
    schnorr::Schnorr,
    sponge::ShakeSponge,
    utils::absorb_curve,
};

const LIMBS: usize = 16;
const NON_FINAL_LIMB_SIZE: usize = 256 / 16;
const BYTES_PER_LIMB: usize = NON_FINAL_LIMB_SIZE / 8;
const SECRETS: usize = 2;

pub struct SharePolynomials<F: Field>([DensePolynomial<F>; SECRETS]);

impl<F: PrimeField> SharePolynomials<F> {
    pub fn create<R: RngCore>(rng: &mut R, threshold: usize) -> Self {
        Self(array_init(|_| {
            let mut p = DensePolynomial::<F>::rand(threshold - 1, rng);
            p.coeffs[0] = F::zero();
            p
        }))
    }

    pub fn shares(&self, num_parties: usize) -> Shares<F> {
        let pts = evaluation_points::<F>(num_parties);
        let per_party = (0..num_parties)
            .map(|i| array_init(|k| self.0[k].evaluate(&pts[i][k])))
            .collect_vec();
        Shares { per_party }
    }

    fn commitments<P: SWCurveConfig<ScalarField = F>, R: RngCore>(
        &self,
        rng: &mut R,
        ipa_params: &ipa::Params<P>,
    ) -> [(Affine<P>, F); SECRETS] {
        array_init(|i| {
            let r: F = F::rand(rng);

            let g =
                <Projective<P> as VariableBaseMSM>::msm_unchecked(&ipa_params.h, &self.0[i].coeffs)
                    + ipa_params.blinder_base * r;
            (g.into_affine(), r)
        })
    }
}

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

struct EvaluationIPA<P: SWCurveConfig> {
    lr: Vec<(Affine<P>, Affine<P>)>,
    schnorr: Schnorr<3, P>,
}

struct SimpleEvaluationIPA<P: SWCurveConfig> {
    lr: Vec<(Affine<P>, Affine<P>)>,
    schnorr: Schnorr<2, P>,
}

struct BooleanityProof<P: SWCurveConfig> {
    lr: Vec<(Affine<P>, Affine<P>)>,
    quotient: Affine<P>,
    bit_commitment_eval: P::ScalarField,
    quotient_eval: P::ScalarField,
    schnorr: Schnorr<2, P>,
}

struct Proof<P: SWCurveConfig> {
    bit_packing: BitpackingIPA<P>,
    booleanity: BooleanityProof<P>,
    polynomials: [Affine<P>; SECRETS],
    evaluation: [EvaluationIPA<P>; SECRETS],
    secrets_agree: SimpleEvaluationIPA<P>,
}

pub struct EncryptedSharesWithProof<P: SWCurveConfig> {
    shares: EncryptedShares<P>,
    proof: Proof<P>,
}

impl<P: GLVConfig> EncryptedSharesWithProof<P> {
    pub fn decrypt_and_verify<'a>(
        &self,
        encryption_params: &EncryptionParams<Affine<P>>,
        plonk_params: &PLONKIPAParams<'a, P>,
        table: &DLogTable<P>,
        secret_key: P::ScalarField,
        i: usize,
        public_keys: &Vec<Affine<P>>,
        threshold: usize,
    ) -> Option<[P::ScalarField; 2]> {
        if self.verify(encryption_params, plonk_params, public_keys, threshold) {
            let shares: SinglePartyEncryptedShares<Affine<P>> = SinglePartyEncryptedShares {
                by_limb: &self.shares.per_party[i],
                randomness: &self.shares.randomness,
            };

            Some(decrypt(shares, table, secret_key))
        } else {
            None
        }
    }

    pub fn verify<'a>(
        &self,
        encryption_params: &EncryptionParams<Affine<P>>,
        plonk_params: &PLONKIPAParams<'a, P>,
        public_keys: &Vec<Affine<P>>,
        threshold: usize,
    ) -> bool {
        let num_parties = public_keys.len();
        let ipa_params = plonk_params.ipa;
        let mut sponge = ShakeSponge::new(&());
        let Proof {
            booleanity,
            bit_packing,
            polynomials,
            evaluation,
            secrets_agree,
        } = &self.proof;

        let sponge = &mut sponge;
        self.shares
            .randomness
            .iter()
            .for_each(|rs| rs.iter().for_each(|r| absorb_curve(sponge, &r)));
        self.shares.per_party.iter().for_each(|p| {
            p.iter()
                .for_each(|ss| ss.iter().for_each(|s| absorb_curve(sponge, &s)))
        });
        self.proof
            .polynomials
            .iter()
            .for_each(|g| absorb_curve(sponge, &g));
        absorb_curve(sponge, &self.proof.bit_packing.bit_commitment);

        let chals = Challenges::create(sponge);

        let combined_public_key = chals.combined_public_key(public_keys).into_affine();

        if !bit_packing.verify(
            ipa_params,
            encryption_params,
            sponge,
            &self.shares,
            num_parties,
            combined_public_key,
            &chals,
        ) {
            return false;
        }

        for (k, e) in evaluation.iter().enumerate() {
            if !e.verify(
                ipa_params,
                polynomials[k],
                k,
                threshold,
                chals.alpha,
                &self.shares,
                public_keys,
                combined_public_key,
                sponge,
            ) {
                return false;
            }
        }

        if !secrets_agree.verify(
            ipa_params,
            (polynomials[0] - polynomials[1]).into_affine(),
            threshold,
            P::ScalarField::zero(),
            P::ScalarField::zero(),
            sponge,
        ) {
            return false;
        }

        if !booleanity.verify(
            &plonk_params.domain,
            &bit_packing.bit_commitment,
            plonk_params,
            sponge,
        ) {
            return false;
        }
        true
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

fn limb_size<F: PrimeField>(i: usize) -> usize {
    let final_limb_size = F::MODULUS_BIT_SIZE as usize % NON_FINAL_LIMB_SIZE;
    if i < LIMBS - 1 {
        NON_FINAL_LIMB_SIZE
    } else {
        final_limb_size
    }
}

struct Challenges<P: SWCurveConfig> {
    alpha: P::ScalarField,
    beta: P::ScalarField,
    gamma: P::ScalarField,
    delta: P::ScalarField,
}

impl<P: SWCurveConfig> Challenges<P> {
    fn combined_public_key(&self, public_keys: &Vec<Affine<P>>) -> Projective<P> {
        <Projective<P> as VariableBaseMSM>::msm(
            public_keys,
            &pows(self.alpha).take(public_keys.len()).collect_vec(),
        )
        .unwrap()
    }

    fn create<S: CryptographicSponge>(sponge: &mut S) -> Self {
        let x = sponge.squeeze_field_elements::<P::ScalarField>(4);
        Self {
            alpha: x[0],
            beta: x[1],
            gamma: x[2],
            delta: x[3],
        }
    }

    // Coefficients are
    // for i in 0..num_parties
    // for j in 0..LIMBS
    // for k in 0..SECRETS
    // for l in 0..(num bits of limb L (the final limb is short))
    // alpha^i beta^j gamma^k 2^l
    //
    // followed by
    // 0 (to allow for any coefficient in subsequent positions)
    fn bit_packing_coefficients(&self, num_parties: usize) -> Vec<P::ScalarField> {
        let Self {
            alpha,
            beta,
            gamma,
            delta: _,
        } = &self;

        let mut public = vec![];
        let mut alpha_i = P::ScalarField::one();
        for _i in 0..num_parties {
            let mut alpha_i_beta_j = alpha_i;
            for j in 0..LIMBS {
                let mut alpha_i_beta_j_gamma_k = alpha_i_beta_j;
                for _k in 0..2 {
                    // 2^l * alpha^i * beta^j * gamma^k
                    let mut c = alpha_i_beta_j_gamma_k;
                    for _l in 0..limb_size::<P::ScalarField>(j) {
                        public.push(c);
                        c.double_in_place();
                    }
                    alpha_i_beta_j_gamma_k *= gamma;
                }
                alpha_i_beta_j *= beta;
            }
            alpha_i *= alpha;
        }
        let padding = (1 << log2(public.len())) - public.len();
        // Need some empty slots to allow us to randomize for the PLONK-type argument
        assert!(padding > 0);
        // allow any value in the committed vector at the remaining positions
        public.extend((0..padding).map(|_| P::ScalarField::zero()));
        assert_eq!(public.len(), 1 << log2(public.len()));

        // pad
        /*
                let padding = (1 << log2(public.len()) as usize) - public.len();
                public.extend((0..padding).map(|_| P::ScalarField::zero()));
        */
        public
    }
}

struct BitsWithCommitment<P: SWCurveConfig> {
    coeffs: Vec<P::ScalarField>,
    comm: Affine<P>,
    blinder: P::ScalarField,
}

impl ShareLimbs {
    fn bits_with_commitment<P: GLVConfig, R: RngCore>(
        &self,
        ipa_params: &ipa::Params<P>,
        rng: &mut R,
    ) -> BitsWithCommitment<P> {
        let num_parties = self.per_party.len();
        let mut coeffs: Vec<P::ScalarField> = vec![];
        let bit_commitment_blinder = P::ScalarField::rand(rng);
        // TODO: Use a batch affine version if efficiency is needed.
        let mut bit_commitment = ipa_params.blinder_base * bit_commitment_blinder;
        let mut idx = 0;
        for i in 0..num_parties {
            for j in 0..LIMBS {
                for k in 0..2 {
                    for l in 0..limb_size::<P::ScalarField>(j) {
                        let b = (self.per_party[i][j][k] >> l) & 1;
                        if b == 1 {
                            bit_commitment += ipa_params.h[idx];
                        }
                        coeffs.push(P::ScalarField::from_bigint(b.into()).unwrap());
                        idx += 1;
                    }
                }
            }
        }
        let final_random_value = P::ScalarField::rand(rng);
        coeffs.push(final_random_value);
        bit_commitment += ipa_params.h[idx] * final_random_value;
        let bit_commitment = bit_commitment.into_affine();
        BitsWithCommitment {
            coeffs,
            comm: bit_commitment,
            blinder: bit_commitment_blinder,
        }
    }
}

impl<P: GLVConfig> EncryptedShares<P> {
    // \delta \sum_jk \beta^j \gamma^k R_jk + sum_ijk \alpha^i \beta^j \gamma^k C_ijk
    fn combined_commitment(&self, chals: &Challenges<P>) -> Projective<P> {
        let Challenges {
            alpha,
            beta,
            gamma,
            delta,
        } = &chals;

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
            let mut yrs = batch_glv_mul(&rs, secret_key);
            batch_negate_in_place(&mut yrs);
            let mut denoms = vec![P::BaseField::zero(); num_secrets];
            batch_add_assign_no_branch(&mut denoms, &mut yrs, &cs);
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

pub fn encrypt<'a, R: RngCore, P: GLVConfig + SWCurveConfig>(
    params: &EncryptionParams<Affine<P>>,
    plonk_params: &PLONKIPAParams<'a, P>,
    // The table is a table of powers of ipa_params.inner_product_base
    table: &DLogTable<P>,
    polynomials: &SharePolynomials<P::ScalarField>,
    // limbs: &ShareLimbs,
    public_keys: &Vec<Affine<P>>,
    rng: &mut R,
) -> EncryptedSharesWithProof<P> {
    let shares = polynomials.shares(public_keys.len());
    let limbs = shares.to_limbs();
    let num_secrets = limbs.per_party[0][0].len();

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
            map2(&by_limb, &rs, |v, r| {
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

    let ipa_params = plonk_params.ipa;

    let poly_comms = polynomials.commitments(rng, ipa_params);

    let bits = limbs.bits_with_commitment(ipa_params, rng);

    let mut sponge = ShakeSponge::new(&());
    let sponge = &mut sponge;
    encrypted_shares
        .randomness
        .iter()
        .for_each(|rs| rs.iter().for_each(|r| absorb_curve(sponge, &r)));
    encrypted_shares.per_party.iter().for_each(|p| {
        p.iter()
            .for_each(|ss| ss.iter().for_each(|s| absorb_curve(sponge, &s)))
    });
    poly_comms
        .iter()
        .for_each(|(g, _r)| absorb_curve(sponge, &g));
    absorb_curve(sponge, &bits.comm);

    let chals = Challenges::create(sponge);
    let num_parties = public_keys.len();
    let combined_public_key = chals.combined_public_key(public_keys).into_affine();

    let bitpacking_ipa = BitpackingIPA::create(
        ipa_params,
        &rs,
        params,
        num_parties,
        combined_public_key,
        &chals,
        &bits,
        sponge,
        rng,
    );

    let evaluation = array_init(|k| {
        EvaluationIPA::create(
            ipa_params,
            &polynomials.0[k],
            poly_comms[k].1,
            k,
            chals.alpha,
            &rs,
            public_keys,
            combined_public_key,
            sponge,
            rng,
        )
    });

    // Prove the difference of the 2 polynomials evaluates to 0 at 0.
    let secrets_agree = SimpleEvaluationIPA::create(
        ipa_params,
        &(&polynomials.0[0] - &polynomials.0[1]),
        poly_comms[0].1 - poly_comms[1].1,
        P::ScalarField::zero(),
        sponge,
        rng,
    );

    let booleanity = BooleanityProof::create(plonk_params, &bits, num_parties, sponge, rng);

    EncryptedSharesWithProof {
        shares: encrypted_shares,
        proof: Proof {
            booleanity,
            bit_packing: bitpacking_ipa,
            polynomials: map(&poly_comms, |(g, _)| g),
            evaluation,
            secrets_agree,
        },
    }
}

pub struct EncryptionParams<G> {
    pub public_key_base: G,
}

// Let num_bits = 255 * SECRETS * num_parties
// Let b_0,...,b_{num_bits - 1} be all the bits
// Let C_ijk be the cipher texts
// Let B = 2^16 be the limb base
// Let Y_i be the public key of party i
//
// A proof of:
// exists A b_0,...., b_{num_bits - 1}
// exists m_ijk
// exists r_jk
// bit_commitment = sum_{i < num_bits} b_i H_i +  msm(A, H_{num_bits..})
// and
// forall i j k. C_ijk = m_ijk G + r_jk Y_i
// and
// forall i j k. m_ijk = sum_l 2^l b_i
//
// The final term of a * H_num_bits in the bit_commitment is used for
// for blinding purposes in the PLONK-type argument proving booleanity
// of the committed values.
pub struct BitpackingIPA<P: SWCurveConfig> {
    bit_commitment: Affine<P>,
    lr: Vec<(Affine<P>, Affine<P>)>,
    schnorr: Schnorr<3, P>,
}

pub struct PLONKIPAParams<'a, P: SWCurveConfig> {
    ipa: &'a ipa::Params<P>,
    // monomial_basis: Vec<Affine<P>>,
    domain: Radix2EvaluationDomain<P::ScalarField>,
    domain2: Radix2EvaluationDomain<P::ScalarField>,
}

impl<'a, P: SWCurveConfig> PLONKIPAParams<'a, P> {
    pub fn new(ipa: &'a ipa::Params<P>, column_size: usize) -> Self {
        let domain = Radix2EvaluationDomain::<P::ScalarField>::new(column_size).unwrap();
        let domain2 = Radix2EvaluationDomain::<P::ScalarField>::new(2 * domain.size()).unwrap();
        assert_eq!(domain.group_gen, domain2.group_gen.square());

        // Act as if the ipa.h bases are lagrange polynomials and reinterpet the coefficient
        // polynomials.
        Self {
            ipa,
            // monomial_basis,
            domain,
            domain2,
        }
    }
}

impl<P: GLVConfig> BooleanityProof<P> {
    fn schnorr_bases(
        h0: Affine<P>,
        public0: P::ScalarField,
        inner_product_base: Affine<P>,
        blinder_base: Affine<P>,
    ) -> [Affine<P>; 2] {
        [
            (h0 + inner_product_base * public0).into_affine(),
            blinder_base,
        ]
    }

    // let S = num_parties * P::ScalarField::MODULUS_BIT_SIZE * SECRETS
    // Prove that
    // for all x in the domain (with the exception of omega^S)
    // bit_commitment(x)^2 - bit_commitment(x) = 0
    // (i.e., x is 0 or 1)
    //
    // We do this by showing that
    // bit_commitment^2 - bit_commitment
    // is divisible by v_H(x) / (x - omega^S)
    // I.e.,
    // exists q such that
    // bit_commitment^2 - bit_commitment = q * v_H(x) / (x - omega^S)
    //
    // bit_commitment has degree n-1, so LHS has degree 2(n - 1).
    // deg(v_H / (x - omega^S)) = n-1 so
    // deg(q) = deg(RHS) - (n - 1) = n-1
    pub fn create<'a, R: RngCore, S: CryptographicSponge>(
        plonk_params: &PLONKIPAParams<'a, P>,
        bits: &BitsWithCommitment<P>,
        num_parties: usize,
        sponge: &mut S,
        rng: &mut R,
    ) -> Self {
        let domain = plonk_params.domain;
        let domain2 = plonk_params.domain2;

        let random_value_position = bits.coeffs.len() - 1;
        assert_eq!(
            random_value_position,
            num_parties * P::ScalarField::MODULUS_BIT_SIZE as usize * SECRETS
        );

        // evaluations of
        // sum_i bits.coeffs[i] lagrange_i
        // over the larger domain
        //
        // bits.coeffs has a uniform random field element in the final location so it is safe to
        // reveal one evaluation of this polynomial.
        let bits_eval = {
            // Pad with zeros
            let bits_poly = {
                let mut evals = bits.coeffs.clone();
                evals.extend(
                    (0..domain.size as usize - evals.len()).map(|_| P::ScalarField::zero()),
                );
                Evaluations::from_vec_and_domain(evals, domain).interpolate()
            };

            bits_poly.evaluate_over_domain(domain2)
        };

        let mut constraint = bits_eval.clone();

        // constraint = (bits^2 - bits)
        constraint
            .evals
            .par_iter_mut()
            .zip(bits_eval.evals.par_iter())
            .for_each(|(x, y)| {
                x.square_in_place();
                *x -= *y;
            });
        let mut constraint = constraint.interpolate();
        // Multiply by (x - omega^random_value_position).
        // (x - A) * sum_{i=0}^d c_i x^i = -A c_0 x^0 + sum_{i=1}^{d+1} (c_{i-1} - A c_i) x^i
        constraint.coeffs.push(P::ScalarField::zero());
        let omega_n = domain.element(random_value_position);
        for i in (1..constraint.coeffs.len()).rev() {
            constraint.coeffs[i] = constraint.coeffs[i - 1] - omega_n * constraint.coeffs[i]
        }
        constraint.coeffs[0] *= -omega_n;

        let (quotient_poly, rem) = constraint.divide_by_vanishing_poly(domain);
        assert!(rem.is_zero());
        assert!(quotient_poly.coeffs.len() <= plonk_params.ipa.h.len());
        let quotient_evals = quotient_poly.evaluate_over_domain(domain);

        let (quotient, quotient_blinder) = {
            let comm =
                <Projective<P> as VariableBaseMSM>::msm(&plonk_params.ipa.h, &quotient_evals.evals)
                    .unwrap();
            let blinder = P::ScalarField::rand(rng);
            (
                (comm + plonk_params.ipa.blinder_base * blinder).into_affine(),
                blinder,
            )
        };

        absorb_curve(sponge, &quotient);

        let chals = sponge.squeeze_field_elements(2);
        let poly_combiner: P::ScalarField = chals[0];
        let evaluation_point = chals[1];

        let lgr = domain.evaluate_all_lagrange_coefficients(evaluation_point);

        let quotient_eval = quotient_evals
            .evals
            .par_iter()
            .zip(lgr.par_iter())
            .map(|(x, y)| *x * y)
            .sum();
        let bit_commitment_eval = bits
            .coeffs
            .par_iter()
            .zip(lgr.par_iter())
            .map(|(x, y)| *x * y)
            .sum();

        let mut combined_poly = quotient_evals;
        combined_poly
            .evals
            .par_iter_mut()
            .for_each(|x| *x *= poly_combiner);
        bits.coeffs
            .par_iter()
            .zip(combined_poly.evals.par_iter_mut())
            .for_each(|(c, x)| *x += c);
        let combined_poly_blinder = bits.blinder + poly_combiner * quotient_blinder;

        let ipa = plonk_params
            .ipa
            .prove(sponge, rng, combined_poly.evals, lgr);

        let schnorr_bases = Self::schnorr_bases(
            ipa.h0,
            ipa.public0,
            plonk_params.ipa.inner_product_base,
            plonk_params.ipa.blinder_base,
        );

        let schnorr = Schnorr::prove(
            &schnorr_bases,
            &[ipa.a0, ipa.blinder + combined_poly_blinder],
            sponge,
            rng,
        );

        BooleanityProof {
            bit_commitment_eval,
            quotient_eval,
            quotient,
            lr: ipa.lr,
            schnorr,
        }
    }

    pub fn verify<'a, S: CryptographicSponge>(
        &self,
        domain: &Radix2EvaluationDomain<P::ScalarField>,
        bit_commitment: &Affine<P>,
        plonk_params: &PLONKIPAParams<'a, P>,
        sponge: &mut S,
    ) -> bool {
        let Self {
            bit_commitment_eval,
            quotient_eval,
            quotient,
            lr,
            schnorr,
        } = &self;

        absorb_curve(sponge, quotient);
        let chals = sponge.squeeze_field_elements(2);
        let poly_combiner: P::ScalarField = chals[0];
        let evaluation_point = chals[1];

        let combined_poly = *quotient * poly_combiner + bit_commitment;
        let combined_evaluation = *quotient_eval * poly_combiner + bit_commitment_eval;
        let eval_commitment = plonk_params.ipa.inner_product_base * combined_evaluation;

        let public = domain.evaluate_all_lagrange_coefficients(evaluation_point);
        let ipa::VerifierOutput {
            h0,
            public0,
            lr_sum,
        } = ipa::verify(&plonk_params.ipa.h, sponge, public, lr);

        let schnorr_bases = Self::schnorr_bases(
            h0.into_affine(),
            public0,
            plonk_params.ipa.inner_product_base,
            plonk_params.ipa.blinder_base,
        );

        schnorr.verify(
            eval_commitment + combined_poly + lr_sum,
            &schnorr_bases,
            sponge,
        )
    }
}

impl<P: GLVConfig> SimpleEvaluationIPA<P> {
    fn schnorr_bases(
        h0: Affine<P>,
        public0: P::ScalarField,
        inner_product_base: Affine<P>,
        blinder_base: Affine<P>,
    ) -> [Affine<P>; 2] {
        [
            (h0 + inner_product_base * public0).into_affine(),
            blinder_base,
        ]
    }

    pub fn create<R: RngCore, S: CryptographicSponge>(
        ipa_params: &ipa::Params<P>,
        polynomial: &DensePolynomial<P::ScalarField>,
        polynomial_blinder: P::ScalarField,
        evaluation_point: P::ScalarField,
        sponge: &mut S,
        rng: &mut R,
    ) -> Self {
        let public = pows(evaluation_point)
            .take(polynomial.degree() + 1)
            .collect_vec();

        let ipa = ipa_params.prove(sponge, rng, polynomial.coeffs.clone(), public);

        let schnorr_bases = Self::schnorr_bases(
            ipa.h0,
            ipa.public0,
            ipa_params.inner_product_base,
            ipa_params.blinder_base,
        );

        let schnorr_s = [ipa.a0, polynomial_blinder + ipa.blinder];
        let schnorr = Schnorr::<2, P>::prove(&schnorr_bases, &schnorr_s, sponge, rng);

        SimpleEvaluationIPA {
            lr: ipa.lr,
            schnorr,
        }
    }

    pub fn verify<S: CryptographicSponge>(
        &self,
        ipa_params: &ipa::Params<P>,
        polynomial: Affine<P>,
        degree: usize,
        evaluation_point: P::ScalarField,
        evaluation: P::ScalarField,
        sponge: &mut S,
        // chals: &BitpackingIPAChallenges<P>,
        // c_0: Projective<P>,
    ) -> bool {
        let Self { lr, schnorr } = &self;

        let combined_commitment = ipa_params.inner_product_base * evaluation;

        let ipa::VerifierOutput {
            h0,
            public0,
            lr_sum,
        } = ipa::verify(
            &ipa_params.h,
            sponge,
            pows(evaluation_point).take(degree + 1).collect_vec(),
            lr,
        );

        let schnorr_bases = Self::schnorr_bases(
            h0.into_affine(),
            public0,
            ipa_params.inner_product_base,
            ipa_params.blinder_base,
        );

        schnorr.verify(
            combined_commitment + polynomial + lr_sum,
            &schnorr_bases,
            sponge,
        )
    }
}

impl<P: GLVConfig> EvaluationIPA<P> {
    fn schnorr_bases(
        h0: Affine<P>,
        public0: P::ScalarField,
        inner_product_base: Affine<P>,
        combined_public_key: Affine<P>,
        blinder_base: Affine<P>,
    ) -> [Affine<P>; 3] {
        [
            (h0 + inner_product_base * public0).into_affine(),
            combined_public_key,
            blinder_base,
        ]
    }

    pub fn combined_powers(
        num_parties: usize,
        k: usize,
        degree: usize,
        alpha: P::ScalarField,
    ) -> Vec<P::ScalarField> {
        let pts = evaluation_points(num_parties)
            .into_iter()
            .map(|x| x[k])
            .collect_vec();
        // sum_i alpha^i pows(pts[i])
        let mut res = pows(pts[num_parties - 1]).take(degree + 1).collect_vec();

        // sum_i alpha^i pows(pts[i])
        for i in (0..num_parties - 1).rev() {
            res.par_iter_mut().for_each(|x| *x = alpha * *x);
            for (x, p) in res.iter_mut().zip(pows(pts[i])) {
                *x = p + *x
            }
        }
        res
    }

    pub fn create<R: RngCore, S: CryptographicSponge>(
        ipa_params: &ipa::Params<P>,
        polynomial: &DensePolynomial<P::ScalarField>,
        polynomial_blinder: P::ScalarField,
        k: usize,
        alpha: P::ScalarField,
        encryption_randomness: &[[P::ScalarField; 2]; LIMBS],
        public_keys: &[Affine<P>],
        combined_public_key: Affine<P>,
        sponge: &mut S,
        rng: &mut R,
    ) -> Self {
        let b = P::ScalarField::from_bigint((1u64 << NON_FINAL_LIMB_SIZE).into()).unwrap();
        let num_parties = public_keys.len();

        // r = sum_ij b^j r_jk
        let r = pows(b)
            .zip(encryption_randomness.iter().map(|r| r[k]))
            .map(|(b_j, r_jk)| b_j * r_jk)
            .sum();

        let public = Self::combined_powers(num_parties, k, polynomial.coeffs.len() - 1, alpha);

        let mut sponge_clone = sponge.clone();
        let ipa = ipa_params.prove(sponge, rng, polynomial.coeffs.clone(), public);

        let schnorr_bases = Self::schnorr_bases(
            ipa.h0,
            ipa.public0,
            ipa_params.inner_product_base,
            combined_public_key,
            ipa_params.blinder_base,
        );

        let schnorr_s = [ipa.a0, r, polynomial_blinder + ipa.blinder];
        // exists r.
        // c_0 + lr_sum
        // = (a * (h0 + public0 * inner_product_base)) +
        let schnorr = Schnorr::<3, P>::prove(&schnorr_bases, &schnorr_s, sponge, rng);

        EvaluationIPA {
            lr: ipa.lr,
            schnorr,
        }
    }

    pub fn verify<S: CryptographicSponge>(
        &self,
        ipa_params: &ipa::Params<P>,
        polynomial: Affine<P>,
        k: usize,
        threshold: usize,
        alpha: P::ScalarField,
        encrypted_shares: &EncryptedShares<P>,
        public_keys: &[Affine<P>],
        combined_public_key: Affine<P>,
        sponge: &mut S,
        // chals: &BitpackingIPAChallenges<P>,
        // c_0: Projective<P>,
    ) -> bool {
        let Self { lr, schnorr } = &self;

        let b = P::ScalarField::from_bigint((1u64 << NON_FINAL_LIMB_SIZE).into()).unwrap();
        let num_parties = public_keys.len();

        // combined_commitment = sum_ij alpha^i b^j C_ijk
        let combined_commitment = {
            let mut bases = vec![];
            let mut scalars = vec![];

            let mut alpha_i = P::ScalarField::one();
            for i in 0..num_parties {
                let mut alpha_i_b_j = alpha_i;
                for j in 0..LIMBS {
                    bases.push(encrypted_shares.per_party[i][j][k]);
                    scalars.push(alpha_i_b_j);

                    alpha_i_b_j *= b;
                }
                alpha_i *= alpha;
            }

            <Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };

        let ipa::VerifierOutput {
            h0,
            public0,
            lr_sum,
        } = ipa::verify(
            &ipa_params.h,
            sponge,
            Self::combined_powers(num_parties, k, threshold - 1, alpha),
            lr,
        );

        // Check lr_sum + c_0 == ()
        // Need to verify knowledge of a, s, t  such that
        //
        // C_0 + lr_sum
        // = (a * (h0 + public0 * inner_product_base)) + t (Y + \delta G) + s * blinder_base

        let schnorr_bases = Self::schnorr_bases(
            h0.into_affine(),
            public0,
            ipa_params.inner_product_base,
            combined_public_key,
            ipa_params.blinder_base,
        );

        schnorr.verify(
            combined_commitment + polynomial + lr_sum,
            &schnorr_bases,
            sponge,
        )
    }
}

impl<P: GLVConfig> BitpackingIPA<P> {
    fn schnorr_bases(
        h0: Affine<P>,
        public0: P::ScalarField,
        inner_product_base: Affine<P>,
        delta: P::ScalarField,
        combined_public_key: Affine<P>,
        public_key_base: Affine<P>,
        blinder_base: Affine<P>,
    ) -> [Affine<P>; 3] {
        [
            (h0 + inner_product_base * public0).into_affine(),
            (combined_public_key + (public_key_base * delta)).into_affine(),
            blinder_base,
        ]
    }

    fn create<R: RngCore, S: CryptographicSponge>(
        ipa_params: &ipa::Params<P>,
        encryption_randomness: &[[P::ScalarField; 2]; LIMBS],
        encryption_params: &EncryptionParams<Affine<P>>,
        num_parties: usize,
        combined_public_key: Affine<P>,
        chals: &Challenges<P>,
        bits: &BitsWithCommitment<P>,
        sponge: &mut S,
        rng: &mut R,
    ) -> BitpackingIPA<P> {
        // TODO: Use a batch affine version if efficiency is needed.
        // let chals = encrypted_shares.challenges(sponge);

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

        let ipa = ipa_params.prove(
            sponge,
            rng,
            // Don't really need to clone this
            bits.coeffs.clone(),
            chals.bit_packing_coefficients(num_parties),
        );

        let schnorr_bases = Self::schnorr_bases(
            ipa.h0,
            ipa.public0,
            ipa_params.inner_product_base,
            chals.delta,
            combined_public_key,
            encryption_params.public_key_base,
            ipa_params.blinder_base,
        );

        let schnorr = Schnorr::prove(
            &schnorr_bases,
            &[ipa.a0, r, bits.blinder + ipa.blinder],
            sponge,
            rng,
        );

        BitpackingIPA {
            bit_commitment: bits.comm,
            lr: ipa.lr,
            schnorr,
        }
    }

    fn verify<S: CryptographicSponge>(
        &self,
        ipa_params: &ipa::Params<P>,
        encryption_params: &EncryptionParams<Affine<P>>,
        sponge: &mut S,
        encrypted_shares: &EncryptedShares<P>,
        num_parties: usize,
        combined_public_key: Affine<P>,
        chals: &Challenges<P>,
    ) -> bool {
        let Self {
            bit_commitment,
            lr,
            schnorr,
        } = &self;

        let c_0 = encrypted_shares.combined_commitment(&chals) + bit_commitment;

        let public = chals.bit_packing_coefficients(num_parties);

        let ipa::VerifierOutput {
            h0,
            public0,
            lr_sum,
        } = ipa::verify(&ipa_params.h, sponge, public, lr);

        // Check lr_sum + c_0 == ()
        // Need to verify knowledge of a, s, t  such that
        //
        // C_0 + lr_sum
        // = (a * (h0 + public0 * inner_product_base)) + t (Y + \delta G) + s * blinder_base

        let schnorr_bases = Self::schnorr_bases(
            h0.into_affine(),
            public0,
            ipa_params.inner_product_base,
            chals.delta,
            combined_public_key,
            encryption_params.public_key_base,
            ipa_params.blinder_base,
        );

        schnorr.verify(c_0 + lr_sum, &schnorr_bases, sponge)
    }
}
