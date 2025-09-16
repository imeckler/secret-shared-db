use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::{
    CurveGroup, VariableBaseMSM,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::UniformRand;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::RngCore;
use array_init::array_init;

use crate::utils::absorb_curve;

#[derive(CanonicalDeserialize, CanonicalSerialize)]
pub struct Schnorr<const N: usize, P: SWCurveConfig> {
    z: [P::ScalarField; N],
    rg: Affine<P>,
}

impl<const N: usize, P: SWCurveConfig> Schnorr<N, P> {
    pub fn verify<S: CryptographicSponge>(
        &self,
        comm: Projective<P>,
        g: &[Affine<P>],
        sponge: &mut S,
    ) -> bool {
        absorb_curve(sponge, &self.rg);
        let c = sponge.squeeze_field_elements::<P::ScalarField>(1)[0];
        let zg = <Projective<P> as VariableBaseMSM>::msm(g, &self.z).unwrap();
        comm * c + self.rg == zg
    }

    pub fn prove<R: RngCore, S: CryptographicSponge>(
        g: &[Affine<P>],
        s: &[P::ScalarField],
        sponge: &mut S,
        rng: &mut R,
    ) -> Self {
        let r: [_; N] = array_init(|_| P::ScalarField::rand(rng));
        let rg = <Projective<P> as VariableBaseMSM>::msm(g, &r)
            .unwrap()
            .into_affine();
        absorb_curve(sponge, &rg);
        let c = sponge.squeeze_field_elements::<P::ScalarField>(1)[0];
        let z = array_init(|i| c * s[i] + r[i]);
        Self { rg, z }
    }
}
