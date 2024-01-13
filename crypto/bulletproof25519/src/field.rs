use zeroize::Zeroize;

use crypto_bigint::{
  U512, U1024, impl_modulus,
  modular::constant_mod::{ResidueParams, Residue},
  NonZero, Encoding, Integer,
};

use ff::{Field, PrimeField, FieldBits, PrimeFieldBits, helpers::sqrt_ratio_generic};

use rand_core::RngCore;

use subtle::{Choice, CtOption, ConstantTimeEq, ConstantTimeLess, ConditionallySelectable};

use core::{
  ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg},
  iter::{Sum, Product},
};

use generic_array::{typenum::U33, GenericArray};

impl_modulus!(
  FieldModulus,
  U512,
  concat!(
    "00000000000000000000000000000000000000000000000000000000000000",
    "05fffffffffffffffffffffffffffffffd0dc6212cfee590f9f26acf3b81df3ac3"
  )
);
type ResidueType = Residue<FieldModulus, { FieldModulus::LIMBS }>;

#[derive(Clone, Copy, PartialEq, Eq, Default, Debug, Zeroize)]
pub struct FieldElement(ResidueType);

// 694752535423897172541425910052127447118617369604688205440845127806694419544771
pub const MODULUS: U512 = U512::from_be_hex(concat!(
  "00000000000000000000000000000000000000000000000000000000000000",
  "05fffffffffffffffffffffffffffffffd0dc6212cfee590f9f26acf3b81df3ac3"
));

pub const ORDER: FieldElement = FieldElement(ResidueType::new(&MODULUS));

// Generator X coordinate created via
// sha512("Bulletproof25519 Generator") =
// 24160648779d1b6e09a632ee5665113f0f47c859f39f806cb4e89e7f6e4de1c2
// 521ff50761c9de5d7242a79fb00611cdb4993d2c6c795f81851d2cc85194b38b
// The first 33 bytes were grabbed, and the first 4 bits were dropped
// This remains completely unbiased since the first 4 bits are never used
pub const G_X: FieldElement = FieldElement(ResidueType::new(&U512::from_be_hex(concat!(
  "00000000000000000000000000000000000000000000000000000000000000",
  "04160648779d1b6e09a632ee5665113f0f47c859f39f806cb4e89e7f6e4de1c252",
))));

const WIDE_MODULUS: U1024 = U1024::from_be_hex(concat!(
  "0000000000000000000000000000000000000000000000000000000000000000",
  "0000000000000000000000000000000000000000000000000000000000000000",
  "00000000000000000000000000000000000000000000000000000000000000",
  "05fffffffffffffffffffffffffffffffd0dc6212cfee590f9f26acf3b81df3ac3"
));

fn reduce(x: U1024) -> ResidueType {
  ResidueType::new(&U512::from_le_slice(
    &x.rem(&NonZero::new(WIDE_MODULUS).unwrap()).to_le_bytes()[..64],
  ))
}

impl ConstantTimeEq for FieldElement {
  fn ct_eq(&self, other: &Self) -> Choice {
    self.0.ct_eq(&other.0)
  }
}

impl ConditionallySelectable for FieldElement {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    FieldElement(ResidueType::conditional_select(&a.0, &b.0, choice))
  }
}

macro_rules! math_op {
  (
    $Value: ident,
    $Other: ident,
    $Op: ident,
    $op_fn: ident,
    $Assign: ident,
    $assign_fn: ident,
    $function: expr
  ) => {
    impl $Op<$Other> for $Value {
      type Output = $Value;
      fn $op_fn(self, other: $Other) -> Self::Output {
        Self($function(self.0, other.0))
      }
    }
    impl $Assign<$Other> for $Value {
      fn $assign_fn(&mut self, other: $Other) {
        self.0 = $function(self.0, other.0);
      }
    }
    impl<'a> $Op<&'a $Other> for $Value {
      type Output = $Value;
      fn $op_fn(self, other: &'a $Other) -> Self::Output {
        Self($function(self.0, other.0))
      }
    }
    impl<'a> $Assign<&'a $Other> for $Value {
      fn $assign_fn(&mut self, other: &'a $Other) {
        self.0 = $function(self.0, other.0);
      }
    }
  };
}

macro_rules! math {
  ($Value: ident, $Factor: ident, $add: expr, $sub: expr, $mul: expr) => {
    math_op!($Value, $Value, Add, add, AddAssign, add_assign, $add);
    math_op!($Value, $Value, Sub, sub, SubAssign, sub_assign, $sub);
    math_op!($Value, $Factor, Mul, mul, MulAssign, mul_assign, $mul);
  };
}

math!(
  FieldElement,
  FieldElement,
  |x: ResidueType, y: ResidueType| x.add(&y),
  |x: ResidueType, y: ResidueType| x.sub(&y),
  |x: ResidueType, y: ResidueType| x.mul(&y)
);

macro_rules! from_wrapper {
  ($uint: ident) => {
    impl From<$uint> for FieldElement {
      fn from(a: $uint) -> FieldElement {
        Self(ResidueType::new(&U512::from(a)))
      }
    }
  };
}

from_wrapper!(u8);
from_wrapper!(u16);
from_wrapper!(u32);
from_wrapper!(u64);
from_wrapper!(u128);

impl Neg for FieldElement {
  type Output = Self;
  fn neg(self) -> Self::Output {
    Self(self.0.neg())
  }
}

impl<'a> Neg for &'a FieldElement {
  type Output = FieldElement;
  fn neg(self) -> Self::Output {
    (*self).neg()
  }
}

impl Sum<FieldElement> for FieldElement {
  fn sum<I: Iterator<Item = FieldElement>>(iter: I) -> FieldElement {
    let mut res = FieldElement::ZERO;
    for item in iter {
      res += item;
    }
    res
  }
}

impl<'a> Sum<&'a FieldElement> for FieldElement {
  fn sum<I: Iterator<Item = &'a FieldElement>>(iter: I) -> FieldElement {
    iter.cloned().sum()
  }
}

impl Product<FieldElement> for FieldElement {
  fn product<I: Iterator<Item = FieldElement>>(iter: I) -> FieldElement {
    let mut res = FieldElement::ONE;
    for item in iter {
      res *= item;
    }
    res
  }
}

impl<'a> Product<&'a FieldElement> for FieldElement {
  fn product<I: Iterator<Item = &'a FieldElement>>(iter: I) -> FieldElement {
    iter.cloned().product()
  }
}

impl Field for FieldElement {
  const ZERO: Self = Self(ResidueType::ZERO);
  const ONE: Self = Self(ResidueType::ONE);

  fn random(mut rng: impl RngCore) -> Self {
    let mut bytes = [0; 128];
    rng.fill_bytes(&mut bytes);
    FieldElement(reduce(U1024::from_le_bytes(bytes)))
  }

  fn square(&self) -> Self {
    FieldElement(self.0.square())
  }
  fn double(&self) -> Self {
    FieldElement(self.0.add(&self.0))
  }

  fn invert(&self) -> CtOption<Self> {
    const NEG_2: FieldElement =
      FieldElement(ResidueType::new(&MODULUS.saturating_sub(&U512::from_u8(2))));
    CtOption::new(self.pow(NEG_2), !self.is_zero())
  }

  fn sqrt(&self) -> CtOption<Self> {
    const P_4: FieldElement = FieldElement(ResidueType::new(
      &MODULUS.saturating_add(&U512::ONE).wrapping_div(&U512::from_u8(4)),
    ));
    CtOption::new(self.pow(P_4), 1.into())
  }

  fn sqrt_ratio(u: &FieldElement, v: &FieldElement) -> (Choice, FieldElement) {
    sqrt_ratio_generic(u, v)
  }
}

impl PrimeField for FieldElement {
  type Repr = GenericArray<u8, U33>;

  // Big endian representation of the modulus
  const MODULUS: &'static str = concat!(
    "00000000000000000000000000000000000000000000000000000000000000",
    "05fffffffffffffffffffffffffffffffd0dc6212cfee590f9f26acf3b81df3ac3"
  );

  const NUM_BITS: u32 = 259;
  const CAPACITY: u32 = 258;

  const TWO_INV: Self = FieldElement(ResidueType::new(&U512::from_u8(2)).invert().0);

  // This was calculated with the method from the ff crate docs
  // SageMath GF(modulus).primitive_element()
  const MULTIPLICATIVE_GENERATOR: Self = Self(ResidueType::new(&U512::from_u8(2))); // TODO
  // This was set per the specification in the ff crate docs
  // The number of leading zero bits in the little-endian bit representation of (modulus - 1)
  const S: u32 = 0; // TODO

  // This was calculated via the formula from the ff crate docs
  // Self::MULTIPLICATIVE_GENERATOR ** ((modulus - 1) >> Self::S)
  const ROOT_OF_UNITY: Self = FieldElement(ResidueType::new(&U512::from_be_hex(
    "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010",
  ))); // TODO
       // Self::ROOT_OF_UNITY.invert()
  const ROOT_OF_UNITY_INV: Self = FieldElement(Self::ROOT_OF_UNITY.0.invert().0);

  // This was calculated via the formula from the ff crate docs
  // Self::MULTIPLICATIVE_GENERATOR ** (2 ** Self::S)
  const DELTA: Self = FieldElement(ResidueType::new(&U512::from_be_hex(
    "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010",
  ))); // TODO

  fn from_repr(bytes: Self::Repr) -> CtOption<Self> {
    let res = U512::from_le_slice(&[bytes.as_ref(), [0; 31].as_ref()].concat());
    CtOption::new(Self(ResidueType::new(&res)), res.ct_lt(&MODULUS))
  }
  fn to_repr(&self) -> Self::Repr {
    let mut repr = GenericArray::<u8, U33>::default();
    repr.copy_from_slice(&self.0.retrieve().to_le_bytes()[..33]);
    repr
  }

  fn is_odd(&self) -> Choice {
    self.0.retrieve().is_odd()
  }

  fn from_u128(num: u128) -> Self {
    Self::from(num)
  }
}

impl PrimeFieldBits for FieldElement {
  type ReprBits = [u8; 33];

  fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
    let mut repr = [0; 33];
    repr.copy_from_slice(&self.to_repr()[..33]);
    repr.into()
  }

  fn char_le_bits() -> FieldBits<Self::ReprBits> {
    let mut repr = [0; 33];
    repr.copy_from_slice(&MODULUS.to_le_bytes()[..33]);
    repr.into()
  }
}

impl FieldElement {
  /// Interpret the value as a little-endian integer, square it, and reduce it into a FieldElement.
  pub fn from_square(value: [u8; 64]) -> FieldElement {
    let value = U512::from_le_bytes(value);
    FieldElement(reduce(U1024::from(value.mul_wide(&value))))
  }

  pub fn pow(&self, other: FieldElement) -> FieldElement {
    let mut table = [FieldElement::ONE; 16];
    table[1] = *self;
    for i in 2..16 {
      table[i] = table[i - 1] * self;
    }

    let mut res = FieldElement::ONE;
    let mut bits = 0;
    for (i, bit) in other.to_le_bits().iter().rev().enumerate() {
      bits <<= 1;
      let mut bit = *bit as u8;
      assert_eq!(bit | 1, 1);
      bits |= bit;
      bit.zeroize();

      if ((i + 1) % 4) == 0 {
        if i != 3 {
          for _ in 0..4 {
            res *= res;
          }
        }
        res *= table[usize::from(bits)];
        bits = 0;
      }
    }
    res
  }
}
