use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use tiny_keccak::{Hasher, Shake, Xof};

#[derive(Clone)]
pub struct ShakeSponge(Shake);

impl CryptographicSponge for ShakeSponge {
    type Config = ();

    fn new(_params: &Self::Config) -> Self {
        ShakeSponge(Shake::v256())
    }

    fn absorb(&mut self, input: &impl Absorb) {
        self.0.update(&input.to_sponge_bytes_as_vec()[..]);
    }

    fn squeeze_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        const BYTES_PER_SQUEEZE: usize = 32;
        let num_squeezes = num_bytes.div_ceil(BYTES_PER_SQUEEZE);

        let mut res = vec![0u8; BYTES_PER_SQUEEZE * num_squeezes];

        for i in 0..num_squeezes {
            self.0
                .squeeze(&mut res[i * BYTES_PER_SQUEEZE..(i + 1) * BYTES_PER_SQUEEZE]);
        }
        res.truncate(num_bytes);
        res
    }

    fn squeeze_bits(&mut self, num_bits: usize) -> Vec<bool> {
        let num_bytes = num_bits.div_ceil(8);
        let bytes = self.squeeze_bytes(num_bytes);
        (0..num_bits)
            .map(|i| {
                let j = i % 8;
                ((bytes[i / 8] >> j) & 1) == 1
            })
            .collect()
    }
}
