use crate::traits::{KeyImageGen, Link, Sign, Verify};
use crate::prelude::*;
use curve25519_dalek::constants;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use digest::generic_array::typenum::U64;
use digest::Digest;
use rand_core::{CryptoRng, RngCore};
use curve25519_dalek::traits::MultiscalarMul;

/// Concise Linkable Spontaneous Anonymous Group (CLSAG) signatures
/// > CLSAG is sort of half-way between bLSAG and MLSAG. Suppose you have a ‘primary’ key, and
/// associated with it are several ‘auxiliary’ keys. It is important to prove knowledge of all
/// private keys, but linkability only applies to the primary. This linkability retraction allows
/// smaller, faster signatures than afforded by MLSAG.
///
/// Please read tests at the bottom of the source code for this module for examples on how to use
/// it
pub struct CLSAG {
    /// This is the challenge generated non-interactievely
    pub challenge: Scalar,
    /// These responses are mostly fake, except one which is real.
    pub responses: Vec<Scalar>,
    /// These are public keys most of which does not belong to the signer, except one which is the
    /// signer.
    pub ring: Vec<Vec<RistrettoPoint>>,
    /// These are key images. Only the first one is linkable. If the keypair corresponding to the
    /// first key-image is ever used everyone will know.
    pub key_images: Vec<RistrettoPoint>,
}

impl KeyImageGen<Vec<Scalar>, Vec<RistrettoPoint>> for CLSAG {
    /// Some signature schemes require the key images to be signed as well.
    /// Use this method to generate them
    fn generate_key_image<Hash: Digest<OutputSize = U64> + Clone + Default>(
        ks: Vec<Scalar>,
    ) -> Vec<RistrettoPoint> {
        let k_points: Vec<RistrettoPoint> = ks
            .iter()
            .map(|k| k * constants::RISTRETTO_BASEPOINT_POINT)
            .collect();

        // This is the base key
        // i.e. the first public key for which the prover has the private key
        let base_key_hashed_to_point: RistrettoPoint =
            RistrettoPoint::from_hash(Hash::default().chain_update(k_points[0].compress().as_bytes()));

        let key_images: Vec<RistrettoPoint> =
            ks.iter().map(|k| k * base_key_hashed_to_point).collect();

        return key_images;
    }
}

impl Sign<Vec<Scalar>, Vec<Vec<RistrettoPoint>>> for CLSAG {
    /// To sign you need `ks` which is the set of private keys you want to sign with. Only the
    /// first one is linkable. The `ring` contains public keys for everybody except you. Your
    /// public key will be inserted into it at random (secret) index. The `message` is what you are signing
    fn sign<
        Hash: Digest<OutputSize = U64> + Clone + Default,
        CSPRNG: CryptoRng + RngCore + Default,
    >(
        ks: Vec<Scalar>,
        mut ring: Vec<Vec<RistrettoPoint>>,
        secret_index: usize,
        message: &Vec<u8>,
    ) -> CLSAG {
        let mut csprng = CSPRNG::default();

        let nr = ring.len() + 1;
        let nc = ring[0].len();

        //Provers public keys
        let k_points: Vec<RistrettoPoint> = ks
            .iter()
            .map(|k| k * constants::RISTRETTO_BASEPOINT_POINT)
            .collect();

        // This is the base key
        // i.e. the first public key for which the prover has the private key
        let base_key_hashed_to_point: RistrettoPoint =
            RistrettoPoint::from_hash(Hash::default().chain_update(k_points[0].compress().as_bytes()));

        let key_images: Vec<RistrettoPoint> = CLSAG::generate_key_image::<Hash>(ks.clone());

        ring.insert(secret_index, k_points.clone());

        let a: Scalar = Scalar::random(&mut csprng);

        let mut rs: Vec<Scalar> = (0..nr).map(|_| Scalar::random(&mut csprng)).collect();

        let mut cs: Vec<Scalar> = (0..nr).map(|_| Scalar::ZERO).collect();

        // Domain separated hashes as required by CSLAG paper
        // The hash functions have a label, and the ring members fed into it
        let prefixed_hashes: Vec<Hash> = (0..nc)
            .map(|index| {
                let mut h: Hash = Hash::default();
                h.update(format!("CSLAG_{}", index));
                for i in 0..nr {
                    for j in 0..nc {
                        h.update(ring[i][j].compress().as_bytes());
                    }
                }
                return h;
            })
            .collect();

        // These prefixed hash functions have a label,
        // and the ring members, and key images fed into it
        let prefixed_hashes_with_key_images: Vec<Hash> = (0..nc)
            .map(|index| {
                let mut h: Hash = prefixed_hashes[index].clone();
                for j in 0..nc {
                    h.update(key_images[j].compress().as_bytes());
                }
                return h;
            })
            .collect();

        let aggregate_private_key: Scalar = (0..nc)
            .map(|j| {
                let h: Hash = prefixed_hashes_with_key_images[j].clone();
                return Scalar::from_hash(h) * ks[j];
            })
            .sum();

        let aggregate_public_keys: Vec<RistrettoPoint> = (0..nr)
            .map(|i| {
                return (0..nc)
                    .map(|j| {
                        let h: Hash = prefixed_hashes_with_key_images[j].clone();
                        return Scalar::from_hash(h.clone()) * ring[i][j];
                    })
                    .sum();
            })
            .collect();

        let aggregate_key_image: RistrettoPoint = (0..nc)
            .map(|j| {
                let h: Hash = prefixed_hashes_with_key_images[j].clone();
                return Scalar::from_hash(h.clone()) * key_images[j];
            })
            .sum();

        let mut hashes: Vec<Hash> = (0..nr)
            .map(|_| {
                let mut h: Hash = Hash::default();
                h.update(format!("CSLAG_c"));
                for i in 0..nr {
                    for j in 0..nc {
                        h.update(ring[i][j].compress().as_bytes());
                    }
                }
                h.update(message);
                return h;
            })
            .collect();

        hashes[(secret_index + 1) % nr].update(
            (a * constants::RISTRETTO_BASEPOINT_POINT)
                .compress()
                .as_bytes(),
        );
        hashes[(secret_index + 1) % nr].update((a * base_key_hashed_to_point).compress().as_bytes());
        cs[(secret_index + 1) % nr] = Scalar::from_hash(hashes[(secret_index + 1) % nr].clone());

        let mut i = (secret_index + 1) % nr;

        loop {
            hashes[(i + 1) % nr].update(
                RistrettoPoint::multiscalar_mul(
                    &[rs[i % nr], cs[i % nr]],
                    &[
                        constants::RISTRETTO_BASEPOINT_POINT,
                        aggregate_public_keys[i % nr]
                    ]
                )
                    .compress()
                    .as_bytes(),
            );
            hashes[(i + 1) % nr].update(
                RistrettoPoint::multiscalar_mul(
                    &[rs[i % nr], cs[i % nr]],
                    &[
                        RistrettoPoint::from_hash(
                            Hash::default().chain_update(
                                ring[i % nr][0].compress().as_bytes()
                            ),
                        ),
                        aggregate_key_image
                    ]
                )
                    .compress()
                    .as_bytes(),
            );
            cs[(i + 1) % nr] = Scalar::from_hash(hashes[(i + 1) % nr].clone());

            if secret_index >= 1 && i % nr == (secret_index - 1) % nr {
                break;
            } else if secret_index == 0 && i % nr == nr - 1 {
                break;
            } else {
                i = (i + 1) % nr;
            }
        }

        rs[secret_index] = a - (cs[secret_index] * aggregate_private_key);

        return CLSAG {
            challenge: cs[0],
            responses: rs,
            ring: ring,
            key_images: key_images,
        };
    }
}

impl Verify for CLSAG {
    /// To verify a `signature` you need the `message` too
    fn verify<Hash: Digest<OutputSize = U64> + Clone + Default>(
        signature: &CLSAG,
        message: &Vec<u8>,
    ) -> bool {
        let nr = signature.ring.len();
        let nc = signature.ring[0].len();

        let mut reconstructed_c: Scalar = signature.challenge;
        // Domain separated hashes as required by CSLAG paper
        // The hash functions have a label, and the ring members fed into it
        let prefixed_hashes: Vec<Hash> = (0..nc)
            .map(|index| {
                let mut h: Hash = Hash::default();
                h.update(format!("CSLAG_{}", index));
                for i in 0..nr {
                    for j in 0..nc {
                        h.update(signature.ring[i][j].compress().as_bytes());
                    }
                }
                return h;
            })
            .collect();

        // These prefixed hash functions have a label,
        // and the ring members, and key images fed into it
        let prefixed_hashes_with_key_images: Vec<Hash> = (0..nc)
            .map(|index| {
                let mut h: Hash = prefixed_hashes[index].clone();
                for j in 0..nc {
                    h.update(signature.key_images[j].compress().as_bytes());
                }
                return h;
            })
            .collect();

        let aggregate_public_keys: Vec<RistrettoPoint> = (0..nr)
            .map(|i| {
                return (0..nc)
                    .map(|j| {
                        let h: Hash = prefixed_hashes_with_key_images[j].clone();
                        return Scalar::from_hash(h.clone()) * signature.ring[i][j];
                    })
                    .sum();
            })
            .collect();

        let aggregate_key_image: RistrettoPoint = (0..nc)
            .map(|j| {
                let h: Hash = prefixed_hashes_with_key_images[j].clone();
                return Scalar::from_hash(h.clone()) * signature.key_images[j];
            })
            .sum();
        for _i in 0..nr {
            let mut h: Hash = Hash::default();
            h.update(format!("CSLAG_c"));
            for i in 0..nr {
                for j in 0..nc {
                    h.update(signature.ring[i][j].compress().as_bytes());
                }
            }
            h.update(message);
            h.update(
                RistrettoPoint::multiscalar_mul(
                    &[signature.responses[_i], reconstructed_c],
                    &[
                        constants::RISTRETTO_BASEPOINT_POINT,
                        aggregate_public_keys[_i]
                    ]
                )
                    .compress()
                    .as_bytes(),
            );

            h.update(
                RistrettoPoint::multiscalar_mul(
                    &[signature.responses[_i], reconstructed_c],
                    &[
                        RistrettoPoint::from_hash(
                            Hash::new().chain_update(
                                signature.ring[_i][0].compress().as_bytes()
                            )
                        ),
                        aggregate_key_image
                    ]
                )
                    .compress()
                    .as_bytes(),
            );
            reconstructed_c = Scalar::from_hash(h);
        }

        return signature.challenge == reconstructed_c;
    }
}

impl Link for CLSAG {
    /// This is for linking two signatures and checking if they are signed by the same person
    fn link(signature_1: CLSAG, signature_2: CLSAG) -> bool {
        return signature_1.key_images[0] == signature_2.key_images[0];
    }
}

#[cfg(test)]
#[cfg(feature = "std")]
mod test {
    extern crate blake2;
    extern crate rand;
    extern crate sha2;
    extern crate sha3;

    use super::*;
    use blake2::Blake2b512;
    use curve25519_dalek::ristretto::RistrettoPoint;
    use curve25519_dalek::scalar::Scalar;
    use rand::rngs::OsRng;
    use sha2::Sha512;
    use sha3::Keccak512;

    #[test]
    fn clsag() {
        let mut csprng = OsRng::default();

        let secret_index = 1;
        let nr = 2;
        let nc = 2;

        let ks: Vec<Scalar> = (0..nc).map(|_| Scalar::random(&mut csprng)).collect();

        // Simulate randomly chosen Public keys (Prover will insert her public keys here later)
        let ring: Vec<Vec<RistrettoPoint>> = (0..(nr - 1)) // Prover is going to add her key into this mix
            .map(|_| {
                (0..nc)
                    .map(|_| RistrettoPoint::random(&mut csprng))
                    .collect()
            })
            .collect();
        let message: Vec<u8> = b"This is the message".iter().cloned().collect();

        {
            let signature =
                CLSAG::sign::<Sha512, OsRng>(ks.clone(), ring.clone(), secret_index, &message);
            let result = CLSAG::verify::<Sha512>(&signature, &message);
            assert!(result);
        }

        {
            let signature =
                CLSAG::sign::<Keccak512, OsRng>(ks.clone(), ring.clone(), secret_index, &message);
            let result = CLSAG::verify::<Keccak512>(&signature, &message);
            assert!(result);
        }

        {
            let signature =
                CLSAG::sign::<Blake2b512, OsRng>(ks.clone(), ring.clone(), secret_index, &message);
            let result = CLSAG::verify::<Blake2b512>(&signature, &message);
            assert!(result);
        }

        let another_ring: Vec<Vec<RistrettoPoint>> = (0..(nr - 1)) // Prover is going to add her key into this mix
            .map(|_| {
                (0..nc)
                    .map(|_| RistrettoPoint::random(&mut csprng))
                    .collect()
            })
            .collect();
        let another_message: Vec<u8> = b"This is another message".iter().cloned().collect();
        let signature_1 = CLSAG::sign::<Blake2b512, OsRng>(
            ks.clone(),
            another_ring.clone(),
            secret_index,
            &another_message,
        );
        let signature_2 =
            CLSAG::sign::<Blake2b512, OsRng>(ks.clone(), ring.clone(), secret_index, &message);
        let result = CLSAG::link(signature_1, signature_2);
        assert!(result);
    }
}
