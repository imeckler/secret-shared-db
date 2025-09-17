use ark_serialize::*;
use sha2::{Digest, Sha512};

use crate::epoch::Epoch;

#[derive(Clone, Copy)]
pub struct Signature(pub ed25519_dalek::Signature);

impl Signature {
    pub fn digest(epoch: &Epoch, msg: &[u8]) -> Sha512 {
        let mut digest: Sha512 = sha2::Sha512::new();
        digest.update(&epoch.to_bytes());
        digest.update(msg);
        digest
    }

    pub fn create(sk: &ed25519_dalek::SigningKey, epoch: &Epoch, msg: &[u8]) -> Signature {
        let context = b"SecretShareDBRefresh";

        let sig = sk
            .sign_prehashed(Self::digest(epoch, msg), Some(context))
            .unwrap();
        Signature(sig)
    }

    pub fn verify(&self, pk: ed25519_dalek::VerifyingKey, epoch: &Epoch, msg: &[u8]) -> bool {
        let context = b"SecretShareDBRefresh";

        pk.verify_prehashed(Self::digest(epoch, msg), Some(context), &self.0)
            .is_ok()
    }
}

impl Valid for Signature {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalSerialize for Signature {
    fn serialized_size(&self, _compress: Compress) -> usize {
        ed25519_dalek::Signature::BYTE_SIZE
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        writer
            .write(&self.0.to_bytes())
            .map_err(|e| ark_serialize::SerializationError::IoError(e))
            .map(|_| ())
    }
}

impl CanonicalDeserialize for Signature {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = [0u8; ed25519_dalek::Signature::BYTE_SIZE];
        reader
            .read_exact(&mut bytes)
            .map_err(|e| ark_serialize::SerializationError::IoError(e))
            .map(|()| Signature(ed25519_dalek::Signature::from_bytes(&bytes)))
    }
}
