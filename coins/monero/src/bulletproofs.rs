#![allow(non_snake_case)]

use curve25519_dalek::{scalar::Scalar, edwards::EdwardsPoint};

use crate::{Commitment, wallet::TransactionError, serialize::*};

pub struct Bulletproofs {
  pub A: EdwardsPoint,
  pub S: EdwardsPoint,
  pub T1: EdwardsPoint,
  pub T2: EdwardsPoint,
  pub taux: Scalar,
  pub mu: Scalar,
  pub L: Vec<EdwardsPoint>,
  pub R: Vec<EdwardsPoint>,
  pub a: Scalar,
  pub b: Scalar,
  pub t: Scalar
}

impl Bulletproofs {
  pub fn new(outputs: &[Commitment]) -> Result<Bulletproofs, TransactionError> {
    if outputs.len() > 16 {
      return Err(TransactionError::TooManyOutputs)?;
    }

    let masks: Vec<[u8; 32]> = outputs.iter().map(|commitment| commitment.mask.to_bytes()).collect();
    let amounts: Vec<u64> = outputs.iter().map(|commitment| commitment.amount).collect();
    let res: Bulletproofs;
    unsafe {
      #[link(name = "wrapper")]
      extern "C" {
        fn free(ptr: *const u8);
        fn c_generate_bp(len: u8, amounts: *const u64, masks: *const [u8; 32]) -> *const u8;
      }

      let ptr = c_generate_bp(outputs.len() as u8, amounts.as_ptr(), masks.as_ptr());
      let len = ((ptr.read() as usize) << 8) + (ptr.add(1).read() as usize);
      res = Bulletproofs::deserialize(
        // Wrap in a cursor to provide a mutable Reader
        &mut std::io::Cursor::new(std::slice::from_raw_parts(ptr.add(2), len))
      ).expect("Couldn't deserialize Bulletproofs from Monero");
      free(ptr);
    }

    Ok(res.into())
  }

  pub fn verify(&self, commitments: &[EdwardsPoint]) -> bool {
    if commitments.len() > 16 {
      return false;
    }

    let mut serialized = Vec::with_capacity((9 + (2 * self.L.len())) * 32);
    self.serialize(&mut serialized).unwrap();
    let commitments: Vec<[u8; 32]> = commitments.iter().map(
      |commitment| (commitment * Scalar::from(8 as u8).invert()).compress().to_bytes()
    ).collect();
    unsafe {
      #[link(name = "wrapper")]
      extern "C" {
        fn c_verify_bp(
          serialized_len: usize,
          serialized: *const u8,
          commitments_len: u8,
          commitments: *const [u8; 32]
        ) -> bool;
      }

      c_verify_bp(serialized.len(), serialized.as_ptr(), commitments.len() as u8, commitments.as_ptr())
    }
  }

  fn serialize_core<
    W: std::io::Write,
    F: Fn(&[EdwardsPoint], &mut W) -> std::io::Result<()>
  >(&self, w: &mut W, specific_write_vec: F) -> std::io::Result<()> {
    write_point(&self.A, w)?;
    write_point(&self.S, w)?;
    write_point(&self.T1, w)?;
    write_point(&self.T2, w)?;
    write_scalar(&self.taux, w)?;
    write_scalar(&self.mu, w)?;
    specific_write_vec(&self.L, w)?;
    specific_write_vec(&self.R, w)?;
    write_scalar(&self.a, w)?;
    write_scalar(&self.b, w)?;
    write_scalar(&self.t, w)
  }

  pub fn signature_serialize<W: std::io::Write>(&self, w: &mut W) -> std::io::Result<()> {
    self.serialize_core(w, |points, w| write_raw_vec(write_point, points, w))
  }

  pub fn serialize<W: std::io::Write>(&self, w: &mut W) -> std::io::Result<()> {
    self.serialize_core(w, |points, w| write_vec(write_point, points, w))
  }

  pub fn deserialize<R: std::io::Read>(r: &mut R) -> std::io::Result<Bulletproofs> {
    let bp = Bulletproofs {
      A: read_point(r)?,
      S: read_point(r)?,
      T1: read_point(r)?,
      T2: read_point(r)?,
      taux: read_scalar(r)?,
      mu: read_scalar(r)?,
      L: read_vec(r, read_point)?,
      R: read_vec(r, read_point)?,
      a: read_scalar(r)?,
      b: read_scalar(r)?,
      t: read_scalar(r)?
    };

    if bp.L.len() != bp.R.len() {
      Err(std::io::Error::new(std::io::ErrorKind::Other, "mismatched L/R len"))?;
    }
    Ok(bp)
  }
}
