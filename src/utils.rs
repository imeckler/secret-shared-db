use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::{
    AffineRepr,
    short_weierstrass::{Affine, SWCurveConfig},
};
use ark_serialize::CanonicalSerialize;
pub fn absorb_curve<P: SWCurveConfig, S: CryptographicSponge>(sponge: &mut S, g: &Affine<P>) {
    let (x, y) = g.xy().unwrap();
    let mut buf = vec![0; P::BaseField::uncompressed_size(&x)];
    x.serialize_uncompressed(&mut buf).ok();
    sponge.absorb(&buf);
    buf.iter_mut().for_each(|x| *x = 0);
    y.serialize_uncompressed(&mut buf).ok();
    sponge.absorb(&buf);
}
