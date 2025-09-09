use ark_crypto_primitives::sponge::{
    CryptographicSponge,
    poseidon::{PoseidonDefaultConfig, PoseidonSponge},
};
use ark_ec::{
    AdditiveGroup, AffineRepr, CurveGroup, PrimeGroup, VariableBaseMSM, pairing::Pairing,
    scalar_mul::glv::GLVConfig, short_weierstrass::SWCurveConfig,
};
use ark_ff::{BigInteger, Field, PrimeField, UniformRand, batch_inversion};
use ark_pallas::{Affine, Fr, PallasConfig, Projective};
use ark_std::rand::{RngCore, SeedableRng, rngs::StdRng};
use combine::batch_glv_mul;
use dlog_table::DLogTable;
use itertools::Itertools;
use lagrange::LagrangePreprocessed;
use rayon::prelude::*;
use sha2::digest::typenum::bit;
use std::collections::HashMap;
mod combine;
mod dlog_table;
mod ipa;
mod lagrange;
// mod schnorr;
mod epoch;
mod secret_sharing;
mod signature;
mod snark;
mod sponge;
use ipa::{Commitment, CommitmentKey, pows};
use secret_sharing::{
    EncryptionParams, ShareLimbs, Shares, SinglePartyEncryptedShares, decrypt, encrypt,
};
use sponge::ShakeSponge;

type NodeId = usize;

struct PublicKeyParams<G> {
    node_public_keys: HashMap<NodeId, G>,
}

/*
struct EncryptionParams<G, M> {
    group_to_message: HashMap<G, M>,
    limb_size: usize,
}

struct CipherText<G> {
    r: G,
    c: Vec<G>,
}

struct SecretSharingInstance<G1, G2> {
    public_keys: Vec<G1>,
    a: Vec<G2>,
    r: G1,
    c: Vec<G2>,
}

struct SecretSharingWitness<F> {
    r: F,
    s: Vec<F>,
}

struct SecretSharingProof<G1, G2, F> {
    f: G1,
    a: G2,
    y: G1,
    z_r: F,
    z_a: F,
}

impl<G: PrimeGroup> EncryptionParams<G, usize> {
    fn init(limb_size: usize) -> Self {
        let mut group_to_message = HashMap::new();
        let one = G::generator();
        let mut g = one;
        for i in 0usize..(1usize << limb_size) {
            group_to_message.insert(g, i).unwrap();
            g += one;
        }
        // let f = (0..tree_height).map(|_| G::rand(rng)).collect();
        EncryptionParams {
            group_to_message,
            limb_size,
        }
    }

    fn encrypt<R: RngCore>(
        &self,
        inputs: Vec<(G, G::ScalarField)>,
        rng: &mut R,
    ) -> Vec<CipherText<G>> {
        fn limb_to_group<G: PrimeGroup>(bits_le: &[bool]) -> G {
            let g = G::generator();
            g.mul_bits_be(bits_le.iter().copied().rev()).add(g)
        }

        let ms: Vec<Vec<G>> = inputs
            .iter()
            .map(|(_pk, m)| {
                m.into_bigint()
                    .to_bits_le()
                    .chunks(self.limb_size)
                    .map(limb_to_group)
                    .collect()
            })
            .collect();

        let by_limb = transpose(ms);

        by_limb
            .into_iter()
            .map(|limb_ms| {
                assert_eq!(limb_ms.len(), inputs.len());
                let r = G::ScalarField::rand(rng);
                let rg = G::generator().mul(r);

                let c: Vec<G> = limb_ms
                    .into_iter()
                    .zip(inputs.iter())
                    .map(|(m, (pk, _))| pk.mul(r).add(m))
                    .collect();
                CipherText { r: rg, c }
            })
            .collect()
    }
}
*/

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
    use crate::snark::*;

    let num_parties = 5;
    let threshold = 3;
    let encryption_params = EncryptionParams {
        public_key_base: random_group_element(b"public_key_base", 0),
    };
    let bitpacking_ipa_params = BitPackingIPAParams::new(num_parties);

    let dlog_table = DLogTable::create(bitpacking_ipa_params.ipa.inner_product_base);

    let shares = Shares::<Fr>::create(&mut rng, num_parties, threshold);

    let secret_keys = (0..num_parties).map(|_| Fr::rand(&mut rng)).collect_vec();
    let public_keys = secret_keys
        .iter()
        .map(|s| encryption_params.public_key_base * s)
        .collect_vec();
    let public_keys = Projective::normalize_batch(&public_keys);

    let start = Instant::now();
    let encrypted_with_proof = encrypt(
        &encryption_params,
        &bitpacking_ipa_params,
        &dlog_table,
        &shares.to_limbs(),
        &public_keys,
        &mut rng,
    );

    println!("encryption/proving {:?}", start.elapsed());

    for i in 0..1 {
        let start = Instant::now();
        let decrypted = encrypted_with_proof
            .decrypt_and_verify(
                &encryption_params,
                &bitpacking_ipa_params,
                &dlog_table,
                secret_keys[i],
                i,
                &public_keys,
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
