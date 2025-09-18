use ark_ec::CurveGroup;
use ark_ff::UniformRand;
use ark_pallas::{Fr, Projective};
use ark_std::rand::SeedableRng;
use dlog_table::DLogTable;
use ipa::random_group_element;
use itertools::Itertools;
use std::collections::HashMap;
mod combine;
mod dlog_table;
mod epoch;
mod ipa;
mod pows;
mod schnorr;
mod sponge;
mod utils;
mod vss;

type NodeId = usize;

struct PublicKeyParams<G> {
    node_public_keys: HashMap<NodeId, G>,
}

fn usize_to_seed(x: usize) -> [u8; 32] {
    let mut res = [0u8; 32];
    for i in 0..32 {
        res[i] = ((x >> (8 * i)) & 256) as u8;
    }
    res
}

fn main() {
    use std::time::Instant;
    let mut rng = ark_std::rand::rngs::StdRng::from_seed([0; 32]);
    use crate::vss::*;

    let num_parties = 5;
    // Need 3 or more to decrypt
    let threshold = 3;
    let encryption_params = EncryptionParams {
        public_key_base: random_group_element(b"public_key_base", 0),
    };
    let num_bits = num_parties * 256 * 2;
    println!("num bits {num_bits}");
    let ipa_params = ipa::Params::new(b"ipa", num_bits);
    let plonk_params = PLONKIPAParams::new(&ipa_params, num_bits);

    let dlog_table = DLogTable::create(ipa_params.inner_product_base);

    let share_polynomials = SharePolynomials::<Fr>::create(&mut rng, threshold);
    let shares = share_polynomials.shares(num_parties);

    let secret_keys = (0..num_parties).map(|_| Fr::rand(&mut rng)).collect_vec();
    let public_keys = secret_keys
        .iter()
        .map(|s| encryption_params.public_key_base * s)
        .collect_vec();
    let public_keys = Projective::normalize_batch(&public_keys);

    let start = Instant::now();
    let encrypted_with_proof = encrypt(
        &encryption_params,
        &plonk_params,
        &dlog_table,
        &share_polynomials,
        &public_keys,
        &mut rng,
    );

    println!("encryption/proving {:?}", start.elapsed());

    for i in 0..1 {
        let start = Instant::now();
        let decrypted = encrypted_with_proof
            .decrypt_and_verify(
                &encryption_params,
                &plonk_params,
                &dlog_table,
                secret_keys[i],
                i,
                &public_keys,
                threshold,
            )
            .unwrap();
        println!("decryption/verifying {:?}", start.elapsed());
        assert_eq!(decrypted, shares.per_party[i])
    }
}

fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
    assert!(!v.is_empty());
    let len = v[0].len();
    let mut iters: Vec<_> = v.into_iter().map(|n| n.into_iter()).collect();
    (0..len)
        .map(|_| {
            iters
                .iter_mut()
                .map(|n| n.next().unwrap())
                .collect::<Vec<T>>()
        })
        .collect()
}
