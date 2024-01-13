use zeroize::Zeroize;

use blake2::{Digest, Blake2b512};

use crate::Ciphersuite;

use bulletproof25519::{ scalar::Scalar, point::Point };

use group::{Group, ff::PrimeField};

/// Ciphersuite for bulletproof25519.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Bulletproof25519;
impl Ciphersuite for Bulletproof25519 {
  type F = Scalar;
  type FI = crypto_bigint::U256;
  type G = Point;
  type H = Blake2b512;

  const ID: &'static [u8] = b"Bulletproof25519";

  fn generator() -> Self::G {
    Point::generator()
  }

  fn hash_to_F(dst: &[u8], msg: &[u8]) -> Self::F {
    let mut hash = Blake2b512::digest(&[dst, msg].concat());
    loop {
      let res = Scalar::from_repr(hash.as_slice()[.. 32].try_into().unwrap());
      if res.is_some().into() {
        return res.unwrap()
      } else {
        hash = Blake2b512::digest(&[dst, &hash].concat());
      }
    }
  }
}
