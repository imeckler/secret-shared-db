use core::num;
use std::{collections::HashMap, time::Instant};

use ark_ec::{
    AffineRepr, CurveGroup, PrimeGroup, ScalarMul,
    scalar_mul::{BatchMulPreprocessing, glv::GLVConfig},
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{BigInteger, Field, PrimeField, UniformRand, Zero, batch_inversion};
use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
use ark_std::rand::RngCore;
use itertools::Itertools;
use rayon::prelude::*;

use crate::{
    combine::{batch_add_assign_no_branch, batch_glv_mul, batch_negate_in_place},
    dlog_table::DLogTable,
    ipa::pows,
};

pub struct Shares<F> {
    pub per_party: Vec<Vec<F>>,
}

pub struct ShareLimbs {
    // By party, then by limb, then by row
    per_party: Vec<Vec<Vec<u16>>>,
}

pub struct EncryptedShares<G> {
    // By limb, then by row
    pub randomness: Vec<Vec<G>>,
    // By party, then by limb, then by row
    pub per_party: Vec<Vec<Vec<G>>>,
}

pub struct SinglePartyEncryptedShares<G> {
    // By limb, then by row
    pub randomness: Vec<Vec<G>>,
    // By limb, then by row
    pub by_limb: Vec<Vec<G>>,
}

pub fn decrypt<P: SWCurveConfig + GLVConfig>(
    shares: &SinglePartyEncryptedShares<Affine<P>>,
    table: &DLogTable<P>,
    secret_key: P::ScalarField,
    z: P::ScalarField,
) -> Vec<P::ScalarField> {
    let num_secrets = shares.by_limb[0].len();
    let mut zs = pows(z).take(num_secrets).collect_vec();
    batch_inversion(&mut zs);
    let zinvs = zs;

    let limbs: Vec<Vec<u16>> = shares
        .by_limb
        .iter()
        .zip(shares.randomness.iter())
        .enumerate()
        .map(|(j, (cs, rs))| {
            let mut yrs = batch_glv_mul(rs, secret_key);
            println!("yrs {j} {}", yrs[1]);
            batch_negate_in_place(&mut yrs);
            let mut denoms = vec![P::BaseField::zero(); num_secrets];
            batch_add_assign_no_branch(&mut denoms, &mut yrs, &cs);
            println!("prescale {j} {}", yrs[1]);
            let gs = yrs;
            let res: Vec<_> = gs
                .par_iter()
                .zip(zinvs.par_iter())
                .map(|(p, z)| P::glv_mul_projective(p.into_group(), *z))
                .collect();
            let res = Projective::normalize_batch(&res);
            println!("res {j} {}", res[1]);
            res.par_iter()
                .map(|g| table.bruteforce_dlog(g).unwrap())
                .collect()
        })
        .collect();

    let num_secrets = limbs[0].len();

    (0..num_secrets)
        .map(|i| {
            // limbs.iter().map(|limb| limb[i]).concat!
            let mut bytes = vec![];
            for limb in limbs.iter() {
                let x = limb[i];
                bytes.push(x as u8);
                bytes.push((x >> 8) as u8);
            }
            <P::ScalarField as PrimeField>::from_le_bytes_mod_order(&bytes[..])
        })
        .collect()
}

fn party_eval_point<F: PrimeField>(i: usize) -> F {
    F::from(F::BigInt::from((i + 1) as u64))
}

pub fn encrypt<R: RngCore, P: GLVConfig + SWCurveConfig>(
    params: &EncryptionParams<Affine<P>>,
    limbs: &ShareLimbs,
    public_keys: &Vec<Affine<P>>,
    z: P::ScalarField,
    rng: &mut R,
) -> EncryptedShares<Affine<P>> {
    let num_limbs = limbs.per_party[0].len();
    println!("{num_limbs}");
    let num_secrets = limbs.per_party[0][0].len();
    println!("start rand");
    let rs: Vec<Vec<P::ScalarField>> = (0..num_limbs)
        .map(|_j| {
            (0..num_secrets)
                .map(|_k| P::ScalarField::rand(rng))
                .collect()
        })
        .collect();
    println!("end rand");
    let start = Instant::now();
    let randomness: Vec<Vec<_>> = rs
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let res: Vec<_> = v
                .par_iter()
                .map(|x| GLVConfig::glv_mul_projective(params.public_key_base.into_group(), *x))
                .collect();
            let res = Projective::<P>::normalize_batch(&res);
            println!("eyo {i}");
            res
        })
        .collect();
    println!("end randomness gen {:?}", start.elapsed());

    let start = Instant::now();
    let gs = {
        let mut zs = pows(z).take(num_secrets).collect_vec();
        batch_inversion(&mut zs);
        params.commitment_base.into_group().batch_mul(&zs)
    };
    println!("gs {:?}", start.elapsed());

    let start = Instant::now();
    let shares: Vec<Vec<Vec<_>>> = limbs
        .per_party
        .iter()
        .zip(public_keys.iter())
        .map(|(by_limb, pk)| {
            let pk_table = BatchMulPreprocessing::new(pk.into_group(), num_secrets);

            by_limb
                .iter()
                .zip(rs.iter())
                .enumerate()
                .map(|(j, (v, r))| {
                    println!("v {j} {}", v[1]);
                    let start = Instant::now();
                    let res: Vec<_> = v
                        .par_iter()
                        .zip(gs.par_iter())
                        .map(|(m, g)| P::mul_affine(g, &[(*m as u64) + 1]))
                        .collect();
                    let mut res = Projective::<P>::normalize_batch(&res);
                    println!("premask {j} {}", res[1]);
                    let mut denoms = vec![P::BaseField::zero(); num_secrets];
                    let start = Instant::now();
                    let pkr = pk_table.batch_mul(r);
                    println!("pkr {j} {}", pkr[0]);
                    batch_add_assign_no_branch(&mut denoms, &mut res, &pkr);
                    println!("masked {j} {}", res[1]);
                    res
                })
                .collect()
        })
        .collect();
    println!("shares {:?}", start.elapsed());
    EncryptedShares {
        randomness,
        per_party: shares,
    }
}

pub struct EncryptionParams<G> {
    pub public_key_base: G,
    pub commitment_base: G,
}

/*
impl<G: PrimeGroup> EncryptionParams<G> {
    pub fn new<R: RngCore>(lagrange: LagrangePreprocessed<G>, rng: &mut R) -> Self {
        EncryptionParams {
            public_key_base: G::rand(rng),
            lagrange,
        }
    }

    pub fn encrypt<R: RngCore>(
        &self,
        limbs: &ShareLimbs,
        public_keys: &Vec<G>,
        rng: &mut R,
    ) -> EncryptedShares<G>
    where
        G::ScalarField: UniformRand,
    {
        let num_limbs = limbs.per_party[0].len();
        let num_secrets = limbs.per_party[0][0].len();
        let rs: Vec<Vec<G::ScalarField>> = (0..num_limbs)
            .map(|_i| {
                (0..num_secrets)
                    .map(|_j| G::ScalarField::rand(rng))
                    .collect()
            })
            .collect();
        let randomness: Vec<Vec<G>> = rs
            .iter()
            .map(|v| v.iter().map(|x| self.public_key_base * *x).collect())
            .collect();

        // TODO: can speed this up significantly if needed given we are multiplying all
        // public keys by the same scalars.
        let per_party = limbs
            .per_party
            .iter()
            .zip(public_keys.iter())
            .map(|(per_limb, pk)| {
                per_limb
                    .iter()
                    .zip(rs.iter())
                    .map(|(x_rows, r_rows)| {
                        x_rows
                            .iter()
                            .zip(r_rows.iter())
                            .enumerate()
                            .map(|(i, (x, r))| {
                                pk.clone() * r
                                    + self.lagrange.byte_powers[i][(x & 256) as usize]
                                    + self.lagrange.shifted_byte_powers[i]
                                        [((x >> 8) & 256) as usize]
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        EncryptedShares {
            randomness,
            per_party,
        }
    }
}
*/

impl<F: PrimeField> Shares<F> {
    pub fn to_limbs(&self) -> ShareLimbs {
        let num_limbs = F::MODULUS_BIT_SIZE.div_ceil(16) as usize;
        let per_party = self
            .per_party
            .iter()
            .map(|shares| {
                let bytes_per_limb = 2;
                let mut by_limb = vec![vec![]; num_limbs];
                for s in shares.iter() {
                    let bytes = s.into_bigint().to_bytes_le();
                    for (i, cs) in bytes.chunks(bytes_per_limb).enumerate() {
                        assert_eq!(cs.len(), 2);
                        by_limb[i].push((cs[0] as u16) + ((cs[1] as u16) << 8));
                    }
                }
                by_limb
            })
            .collect();
        ShareLimbs { per_party }
    }

    pub fn create<R: RngCore>(
        rng: &mut R,
        num_parties: usize,
        threshold: usize,
        num_secrets: usize,
    ) -> Self {
        let mut per_party = vec![vec![]; num_parties];
        for _ in 0..num_secrets {
            let mut p = DensePolynomial::<F>::rand(threshold - 1, rng);
            p.coeffs[0] = F::zero();
            for i in 0..num_parties {
                per_party[i].push(p.evaluate(&party_eval_point(i)));
            }
        }
        Shares { per_party }
    }
}
