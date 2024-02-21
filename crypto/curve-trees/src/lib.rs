#![allow(non_snake_case)]

use core::{marker::PhantomData, fmt::Debug};

use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;
use ciphersuite::{
  group::ff::{Field, PrimeField},
  Ciphersuite,
};

use ecip::Ecip;
use bulletproofs_plus::{
  VectorCommitmentGenerators,
  arithmetic_circuit::*,
  gadgets::{
    elliptic_curve::{Trit, DLogTable, EmbeddedCurveOperations, scalar_to_trits},
    set_membership::assert_variable_in_set_gadget,
  },
};

pub mod pedersen_hash;
pub mod permissible;
use permissible::Permissible;
pub mod tree;
use tree::*;

// #[cfg(test)]
pub mod tests;

pub trait CurveCycle: Clone + Copy + PartialEq + Eq + core::fmt::Debug {
  type C1: Ecip<FieldElement = <Self::C2 as Ciphersuite>::F>
    + EmbeddedCurveOperations<Embedded = Self::C2>;
  type C2: Ecip<FieldElement = <Self::C1 as Ciphersuite>::F>
    + EmbeddedCurveOperations<Embedded = Self::C1>;

  fn c1_coords(
    point: <Self::C1 as Ciphersuite>::G,
  ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F);
  fn c2_coords(
    point: <Self::C2 as Ciphersuite>::G,
  ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F);
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct FlipCurveCycle<C: CurveCycle>(PhantomData<C>);
impl<C: CurveCycle> CurveCycle for FlipCurveCycle<C> {
  type C1 = C::C2;
  type C2 = C::C1;

  fn c1_coords(
    point: <Self::C1 as Ciphersuite>::G,
  ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F) {
    C::c2_coords(point)
  }
  fn c2_coords(
    point: <Self::C2 as Ciphersuite>::G,
  ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F) {
    C::c1_coords(point)
  }
}

pub fn new_blind<R: RngCore + CryptoRng, C1: Ciphersuite, C2: Ciphersuite>(
  rng: &mut R,
  mutual_trits: usize,
  offset: u64,
) -> (C1::F, C2::F) {
  // Generate a candidate within the mutual trit capacity
  let res = loop {
    let candidate = C1::F::random(&mut *rng);
    let trits = scalar_to_trits::<C1>(candidate + C1::F::from(offset));
    if trits.len() <= mutual_trits {
      // TODO: Support divisors when we have an odd amount of points and remove this
      if (trits.iter().filter(|trit| **trit != Trit::Zero).count() % 2) != 1 {
        continue;
      }
      break candidate;
    }
  };

  let mut c2_repr = <C2::F as PrimeField>::Repr::default();
  c2_repr.as_mut().copy_from_slice(res.to_repr().as_ref());
  (res, C2::F::from_repr(c2_repr).unwrap())
}

pub fn layer_gadget<R: RngCore + CryptoRng, T: 'static + Transcript, C: CurveCycle>(
  rng: &mut R,
  circuit: &mut Circuit<T, C::C2>,
  permissible: &Permissible<C::C1>,
  H: &'static DLogTable<C::C1>,
  pedersen_generators: &VectorCommitmentGenerators<T, C::C2>,
  blinded_point: Option<<C::C1 as Ciphersuite>::G>,
  blind: Option<<C::C1 as Ciphersuite>::F>,
  permissibility_offset: u64,
  elements: Vec<Option<<C::C2 as Ciphersuite>::F>>,
  last: bool,
) -> (Option<<C::C2 as Ciphersuite>::F>, Option<<C::C2 as Ciphersuite>::G>) {
  // Unblind the point
  let unblinded = {
    let (blind_x, blind_y) = if let Some(blind) = blind {
      let coords = C::c1_coords(H.generator() * blind);
      (Some(coords.0), Some(coords.1))
    } else {
      (None, None)
    };
    let blind_x = circuit.add_secret_input(blind_x);
    let blind_y = circuit.add_secret_input(blind_y);
    let blind_var = C::C2::constrain_on_curve(circuit, blind_x, blind_y);

    // Prove we know the DLog of the point we're unblinding by to prevent unblinding by arbitrary
    // points
    C::C2::dlog_pok(&mut *rng, circuit, H, blind_var, blind);

    // Perform the addition
    {
      let blinded_point = blinded_point.map(C::c1_coords);
      let blinded_point_x = circuit.add_secret_input(blinded_point.map(|point| point.0));
      let blinded_point_y = circuit.add_secret_input(blinded_point.map(|point| point.1));
      // TODO: We don't need to constrain it's on curve since we know it is
      let blinded_point = C::C2::constrain_on_curve(circuit, blinded_point_x, blinded_point_y);

      let x_prod = circuit.variable_to_product(blinded_point.x()).unwrap();
      let y_prod = circuit.variable_to_product(blinded_point.y()).unwrap();
      circuit.post_constrain_equality(x_prod);
      circuit.post_constrain_equality(y_prod);

      C::C2::incomplete_add(circuit, blind_var, blinded_point)
    }
  };

  // Make sure the point is permissible
  permissible.gadget(circuit, unblinded.y());

  // Create the branch hash
  {
    // Add the elements in this hash
    let mut x_coords = vec![];
    for elem in elements {
      x_coords.push(circuit.add_secret_input(elem));
    }

    let x_coords = {
      let mut prods = vec![];
      let mut i = 0;
      while i < x_coords.len() {
        let (l, r, _) =
          circuit.product(x_coords[i], x_coords.get(i + 1).copied().unwrap_or(x_coords[i])).0;
        prods.push(l);
        prods.push(r);
        i += 2;
      }
      prods.truncate(x_coords.len());
      prods
    };

    // Ensure the unblinded point's x coordinate is actually present in the hash
    assert_variable_in_set_gadget(
      circuit,
      circuit.variable_to_product(unblinded.x()).unwrap(),
      &x_coords,
    );

    // Bind these to the branch hash
    let commitment = circuit.allocate_vector_commitment();
    assert_eq!(pedersen_generators.len(), x_coords.len());
    circuit.bind(commitment, x_coords, Some(pedersen_generators));

    let blind = Some(if last {
      // If this is the last hash, just use the final permissibility offset
      -<C::C2 as Ciphersuite>::F::from(permissibility_offset)
    } else {
      new_blind::<_, C::C1, C::C2>(rng, H.trits(), permissibility_offset).1
    })
    .filter(|_| circuit.prover());
    (
      // Add the permissibility offset so the 'unblinded' Pedersen hash has the blind needed to be
      // permissible
      // TODO: Adding this offset may make the blind no longer mutual
      blind.map(|blind| blind + <C::C2 as Ciphersuite>::F::from(permissibility_offset)),
      circuit.finalize_commitment(commitment, blind.map(|blind| -blind)),
    )
  }
}

pub fn membership_gadget<R: RngCore + CryptoRng, T: 'static + Transcript, C: CurveCycle>(
  rng: &mut R,
  transcript: &mut T,
  circuit_c1: &mut Circuit<T, C::C1>,
  circuit_c2: &mut Circuit<T, C::C2>,
  tree: &Tree<T, C>,
  blinded_point: Option<<C::C1 as Ciphersuite>::G>,
  blind: Option<<C::C1 as Ciphersuite>::F>,
) where
  T::Challenge: Debug,
{
  {
    transcript.domain_separate(b"curve_trees");
    transcript.append_message(b"tree_parameters", tree.parameters_hash());
  }

  // All tree accessses must be consistent for the lifetime of the tree for this baking to work
  // The one exception is depth. New circuit verification statements will be needed for each depth
  let depth = tree.depth();
  let width = tree.width();
  let permissible_c1 = tree.permissible_c1();
  let permissible_c2 = tree.permissible_c2();
  let dlog_table1 = tree.dlog_table1;
  let dlog_table2 = tree.dlog_table2;

  let mut membership =
    blind.map(|blind| tree.membership(blinded_point.unwrap() + (circuit_c1.h() * blind)).unwrap());

  // We do still access the tree's generators later on

  let mut blinded_point = blinded_point.map(Hash::<C>::Even);
  let mut even_blind = None;
  let mut odd_blind = Some(blind);

  for i in 1 ..= depth {
    if (i % 2) == 1 {
      let this_blinded_point = blinded_point.map(|point| {
        let Hash::Even(point) = point else { panic!("blinded_point was odd at odd layer") };
        point
      });

      let (permissibility_offset, elems) = if let Some(membership) = membership.as_mut() {
        let mut elems = vec![];
        let (permissibility_offset, points) = membership.remove(0);
        for point in points {
          let Hash::Even(point) = point else { panic!("odd layer had odd children") };
          elems.push(Some(C::c1_coords(point).0));
        }
        (permissibility_offset, elems)
      } else {
        (0, vec![None; width])
      };

      let (blind, point) = layer_gadget::<_, _, C>(
        rng,
        circuit_c2,
        permissible_c1,
        dlog_table1,
        tree.odd_generators(i).unwrap(),
        this_blinded_point,
        odd_blind.take().unwrap(),
        permissibility_offset,
        elems,
        i == depth,
      );

      blinded_point = point.map(Hash::Odd);
      even_blind = Some(blind);
    } else {
      let this_blinded_point = blinded_point.map(|point| {
        let Hash::Odd(point) = point else { panic!("blinded_point was even at even layer") };
        point
      });

      let (permissibility_offset, elems) = if let Some(membership) = membership.as_mut() {
        let mut elems = vec![];
        let (permissibility_offset, points) = membership.remove(0);
        for point in points {
          let Hash::Odd(point) = point else { panic!("even layer had even children") };
          elems.push(Some(C::c2_coords(point).0));
        }
        (permissibility_offset, elems)
      } else {
        (0, vec![None; width])
      };

      let (blind, point) = layer_gadget::<_, _, FlipCurveCycle<C>>(
        rng,
        circuit_c1,
        permissible_c2,
        dlog_table2,
        tree.even_generators(i).unwrap(),
        this_blinded_point,
        even_blind.take().unwrap(),
        permissibility_offset,
        elems,
        i == depth,
      );

      blinded_point = point.map(Hash::Even);
      odd_blind = Some(blind);
    }
  }

  // TODO: We don't need proofs that the tree root VC is well formed. We can just add it ourselves
}

pub mod monero {
  use rand_core::OsRng;

  use transcript::{Transcript, RecommendedTranscript};

  use pasta_curves::arithmetic::{Coordinates, CurveAffine};
  use multiexp::BatchVerifier;
  use ciphersuite::{
    group::{ff::Field, Group, GroupEncoding, Curve},
    Ciphersuite, Pallas, Vesta,
  };

  use ecip::Ecip;
  use bulletproofs_plus::{
    Generators,
    arithmetic_circuit::{Circuit, ArithmeticCircuitProof},
    gadgets::elliptic_curve::DLogTable,
    tests::generators as generators_fn,
    weighted_inner_product::WipProof,
  };

  use crate::{
    CurveCycle,
    permissible::Permissible,
    tree::{Hash, Tree},
    new_blind, membership_gadget,
  };

  #[derive(Clone, Copy, PartialEq, Eq, Debug)]
  pub struct Pasta {}
  impl CurveCycle for Pasta {
    type C1 = Pallas;
    type C2 = Vesta;

    fn c1_coords(
      point: <Self::C1 as Ciphersuite>::G,
    ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F) {
      Option::<Coordinates<_>>::from(point.to_affine().coordinates())
        .map(|coords| (*coords.x(), *coords.y()))
        .unwrap_or((<Self::C2 as Ciphersuite>::F::ZERO, <Self::C2 as Ciphersuite>::F::ZERO))
    }
    fn c2_coords(
      point: <Self::C2 as Ciphersuite>::G,
    ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F) {
      Option::<Coordinates<_>>::from(point.to_affine().coordinates())
        .map(|coords| (*coords.x(), *coords.y()))
        .unwrap_or((<Self::C1 as Ciphersuite>::F::ZERO, <Self::C1 as Ciphersuite>::F::ZERO))
    }
  }

  pub struct Setup {
    pub pallas_generators: Generators<RecommendedTranscript, Pallas>,
    pub vesta_generators: Generators<RecommendedTranscript, Vesta>,
    pub tree: Tree<RecommendedTranscript, Pasta>,
  }

  pub struct Proof {
    pub pallas_commitments: Vec<<<Pasta as CurveCycle>::C1 as Ciphersuite>::G>,
    pub pallas_vector_commitments: Vec<<<Pasta as CurveCycle>::C1 as Ciphersuite>::G>,
    pub pallas_proof: ArithmeticCircuitProof<Pallas>,
    pub pallas_proofs: Vec<(WipProof<Pallas>, WipProof<Pallas>)>,
    pub vesta_commitments: Vec<<<Pasta as CurveCycle>::C2 as Ciphersuite>::G>,
    pub vesta_vector_commitments: Vec<<<Pasta as CurveCycle>::C2 as Ciphersuite>::G>,
    pub vesta_proof: ArithmeticCircuitProof<Vesta>,
    pub vesta_proofs: Vec<(WipProof<Vesta>, WipProof<Vesta>)>,
  }

  pub fn setup() -> Setup {
    const WIDTH: u64 = 167;
    // This should use a depth of 4, yet that'd take ~128 GB and hours to run
    // TODO
    const MAX_DEPTH: u32 = 2;

    let leaf_randomness = <<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng);

    let mut pallas_generators = generators_fn::<Pallas>(512 * usize::try_from(MAX_DEPTH).unwrap());
    let mut vesta_generators = generators_fn::<Vesta>(512 * usize::try_from(MAX_DEPTH).unwrap());

    let pallas_h = pallas_generators.h().point();
    let vesta_h = vesta_generators.h().point();

    let permissible_c1 = Permissible::<<Pasta as CurveCycle>::C1> {
      h: pallas_h,
      alpha: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
      beta: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
    };
    let permissible_c2 = Permissible::<<Pasta as CurveCycle>::C2> {
      h: vesta_h,
      alpha: <<Pasta as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
      beta: <<Pasta as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
    };

    let max = WIDTH.pow(MAX_DEPTH);
    let tree = Tree::<RecommendedTranscript, Pasta>::new(
      permissible_c1,
      permissible_c2,
      leaf_randomness,
      WIDTH.try_into().unwrap(),
      max,
    );
    tree.whitelist_vector_commitments(&mut pallas_generators, &mut vesta_generators);

    Setup { tree, pallas_generators, vesta_generators }
  }

  pub fn prove(
    setup: &Setup,
    point_in_tree: <<Pasta as CurveCycle>::C1 as Ciphersuite>::G,
  ) -> (<<Pasta as CurveCycle>::C1 as Ciphersuite>::G, Proof) {
    let mut transcript = RecommendedTranscript::new(b"Monero Curve Trees Proof");

    let blind_c1 = new_blind::<_, Pallas, Vesta>(
      &mut OsRng,
      DLogTable::<Pallas>::new(setup.pallas_generators.h().point()).trits(),
      0,
    )
    .0;
    let blinded_point = point_in_tree - (setup.pallas_generators.h().point() * blind_c1);

    // Prove
    let mut circuit_c1 = Circuit::new(setup.pallas_generators.per_proof(), true);
    let mut circuit_c2 = Circuit::new(setup.vesta_generators.per_proof(), true);
    membership_gadget::<_, _, Pasta>(
      &mut OsRng,
      &mut transcript,
      &mut circuit_c1,
      &mut circuit_c2,
      &setup.tree,
      Some(blinded_point),
      Some(blind_c1),
    );

    // Opportunity to transcript anything else relevant
    transcript.append_message(b"blinded_point", blinded_point.to_bytes());
    transcript.append_message(
      b"tree_root",
      match setup.tree.root() {
        Hash::Even(even) => even.to_bytes(),
        Hash::Odd(odd) => odd.to_bytes(),
      },
    );

    let (pallas_commitments, _, pallas_vector_commitments, pallas_proof, pallas_proofs) =
      circuit_c1.prove_with_vector_commitments(&mut OsRng, &mut transcript);
    let (vesta_commitments, _, vesta_vector_commitments, vesta_proof, vesta_proofs) =
      circuit_c2.prove_with_vector_commitments(&mut OsRng, &mut transcript);

    (
      blinded_point,
      Proof {
        pallas_commitments,
        pallas_vector_commitments,
        pallas_proof,
        pallas_proofs,
        vesta_commitments,
        vesta_vector_commitments,
        vesta_proof,
        vesta_proofs,
      },
    )
  }

  pub fn verify(
    setup: &Setup,
    blinded_point: <<Pasta as CurveCycle>::C1 as Ciphersuite>::G,
    proof: Proof,
  ) -> bool {
    let mut transcript = RecommendedTranscript::new(b"Monero Curve Trees Proof");

    let mut circuit_c1 = Circuit::new(setup.pallas_generators.per_proof(), false);
    let mut circuit_c2 = Circuit::new(setup.vesta_generators.per_proof(), false);
    membership_gadget::<_, _, Pasta>(
      &mut OsRng,
      &mut transcript,
      &mut circuit_c1,
      &mut circuit_c2,
      &setup.tree,
      None,
      None,
    );

    transcript.append_message(b"blinded_point", blinded_point.to_bytes());
    transcript.append_message(
      b"tree_root",
      match setup.tree.root() {
        Hash::Even(even) => even.to_bytes(),
        Hash::Odd(odd) => odd.to_bytes(),
      },
    );

    // We need to arrange the points as post-vars
    let mut c1_additional = vec![];
    for (i, commitment) in proof.vesta_vector_commitments.iter().enumerate() {
      if (i % 2) != 1 {
        continue;
      }
      let coords = Pasta::c2_coords(*commitment);
      c1_additional.push(coords.0);
      c1_additional.push(coords.1);
    }
    let blinded_point_coords = Pasta::c1_coords(blinded_point);
    let mut c2_additional = vec![blinded_point_coords.0, blinded_point_coords.1];
    for (i, commitment) in proof.pallas_vector_commitments.iter().enumerate() {
      if (i % 2) != 1 {
        continue;
      }
      let coords = Pasta::c1_coords(*commitment);
      c2_additional.push(coords.0);
      c2_additional.push(coords.1);
    }

    // The caller must check the tree root aligns
    if (setup.tree.depth() % 2) == 1 {
      assert_eq!(Hash::Odd(*proof.vesta_vector_commitments.last().unwrap()), setup.tree.root());
      c1_additional.pop();
      c1_additional.pop();
    } else {
      assert_eq!(Hash::Even(*proof.pallas_vector_commitments.last().unwrap()), setup.tree.root());
      c2_additional.pop();
      c2_additional.pop();
    }

    // TODO: Review this capacity
    let mut verifier_c1 = BatchVerifier::new(3 * 4);
    let mut verifier_c2 = BatchVerifier::new(3 * 4);

    circuit_c1.verification_statement_with_vector_commitments().verify(
      &mut OsRng,
      &mut verifier_c1,
      &mut transcript,
      proof.pallas_commitments,
      proof.pallas_vector_commitments,
      c1_additional,
      proof.pallas_proof,
      proof.pallas_proofs,
    );
    circuit_c2.verification_statement_with_vector_commitments().verify(
      &mut OsRng,
      &mut verifier_c2,
      &mut transcript,
      proof.vesta_commitments,
      proof.vesta_vector_commitments,
      c2_additional,
      proof.vesta_proof,
      proof.vesta_proofs,
    );

    debug_assert!(verifier_c1.verify_vartime());
    debug_assert!(verifier_c2.verify_vartime());
    verifier_c1.verify_vartime() && verifier_c2.verify_vartime()
  }
}

pub mod ed25519_api {
  use rand_core::OsRng;

  use transcript::{Transcript, RecommendedTranscript};

  use multiexp::BatchVerifier;
  use ciphersuite::{
    group::{ff::Field, Group, GroupEncoding},
    Ciphersuite, Ed25519, Bulletproof25519,
  };

  use ecip::Ecip;
  use bulletproofs_plus::{
    Generators,
    arithmetic_circuit::{Circuit, ArithmeticCircuitProof},
    gadgets::elliptic_curve::DLogTable,
    tests::generators as generators_fn,
    weighted_inner_product::WipProof,
  };

  use crate::{
    CurveCycle,
    permissible::Permissible,
    tree::{Hash, Tree},
    new_blind, membership_gadget,
  };

  #[derive(Clone, Copy, PartialEq, Eq, Debug)]
  pub struct Ed25519Tower {}
  impl CurveCycle for Ed25519Tower {
    type C1 = Ed25519;
    type C2 = Bulletproof25519;

    fn c1_coords(
      _: <Self::C1 as Ciphersuite>::G,
    ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F) {
      // TODO: fix this
      (<Self::C2 as Ciphersuite>::F::ONE, <Self::C2 as Ciphersuite>::F::ONE)
    }
    fn c2_coords(
      _: <Self::C2 as Ciphersuite>::G,
    ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F) {
      // TODO: fix this
      (<Self::C1 as Ciphersuite>::F::ONE, <Self::C1 as Ciphersuite>::F::ONE)
    }
  }

  pub struct GeneratorsAndTree {
    pub ed25519_generators: Generators<RecommendedTranscript, Ed25519>,
    pub bulletproof25519_generators: Generators<RecommendedTranscript, Bulletproof25519>,
    pub tree: Tree<RecommendedTranscript, Ed25519Tower>,
  }

  pub struct Proof {
    pub ed25519_commitments: Vec<<<Ed25519Tower as CurveCycle>::C1 as Ciphersuite>::G>,
    pub ed25519_vector_commitments: Vec<<<Ed25519Tower as CurveCycle>::C1 as Ciphersuite>::G>,
    pub ed25519_proof: ArithmeticCircuitProof<Ed25519>,
    pub ed25519_proofs: Vec<(WipProof<Ed25519>, WipProof<Ed25519>)>,
    pub bulletproof25519_commitments: Vec<<<Ed25519Tower as CurveCycle>::C2 as Ciphersuite>::G>,
    pub bulletproof25519_vector_commitments: Vec<<<Ed25519Tower as CurveCycle>::C2 as Ciphersuite>::G>,
    pub bulletproof25519_proof: ArithmeticCircuitProof<Bulletproof25519>,
    pub bulletproof25519_proofs: Vec<(WipProof<Bulletproof25519>, WipProof<Bulletproof25519>)>,
  }

  pub fn init() -> GeneratorsAndTree {
    const WIDTH: u64 = 167;
    // This should use a depth of 4, yet that'd take ~128 GB and hours to run
    // TODO
    const MAX_DEPTH: u32 = 2;

    let leaf_randomness = <<Ed25519Tower as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng);

    let mut ed25519_generators = generators_fn::<Ed25519>(512 * usize::try_from(MAX_DEPTH).unwrap());
    let mut bulletproof25519_generators = generators_fn::<Bulletproof25519>(512 * usize::try_from(MAX_DEPTH).unwrap());

    let ed25519_h = ed25519_generators.h().point();
    let bulletproof25519_h = bulletproof25519_generators.h().point();

    let permissible_c1 = Permissible::<<Ed25519Tower as CurveCycle>::C1> {
      h: ed25519_h,
      alpha: <<Ed25519Tower as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
      beta: <<Ed25519Tower as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
    };
    let permissible_c2 = Permissible::<<Ed25519Tower as CurveCycle>::C2> {
      h: bulletproof25519_h,
      alpha: <<Ed25519Tower as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
      beta: <<Ed25519Tower as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
    };

    let max = WIDTH.pow(MAX_DEPTH);
    let tree = Tree::<RecommendedTranscript, Ed25519Tower>::new(
      permissible_c1,
      permissible_c2,
      leaf_randomness,
      WIDTH.try_into().unwrap(),
      max,
    );

    tree.whitelist_vector_commitments(&mut ed25519_generators, &mut bulletproof25519_generators);

    GeneratorsAndTree { tree, ed25519_generators, bulletproof25519_generators }
  }

  pub fn make_blind(generators_and_tree: &GeneratorsAndTree) -> <Ed25519 as Ciphersuite>::F {
    let blind_c1 = new_blind::<_, Ed25519, Bulletproof25519>(
      &mut OsRng,
      DLogTable::<Ed25519>::new(generators_and_tree.ed25519_generators.h().point()).trits(),
      0,
    )
    .0;
    blind_c1
  }

  pub fn prove(
    generators_and_tree: &GeneratorsAndTree,
    blind: <Ed25519 as Ciphersuite>::F,
    point_in_tree: <<Ed25519Tower as CurveCycle>::C1 as Ciphersuite>::G,
  ) -> (<<Ed25519Tower as CurveCycle>::C1 as Ciphersuite>::G, Proof) {
    let mut transcript = RecommendedTranscript::new(b"Monero Curve Trees Proof");

    let blind_c1 = blind;
    let blinded_point = point_in_tree - (generators_and_tree.ed25519_generators.h().point() * blind_c1);

    // Prove
    let mut circuit_c1 = Circuit::new(generators_and_tree.ed25519_generators.per_proof(), true);
    let mut circuit_c2 = Circuit::new(generators_and_tree.bulletproof25519_generators.per_proof(), true);
    membership_gadget::<_, _, Ed25519Tower>(
      &mut OsRng,
      &mut transcript,
      &mut circuit_c1,
      &mut circuit_c2,
      &generators_and_tree.tree,
      Some(blinded_point),
      Some(blind_c1),
    );

    // Opportunity to transcript anything else relevant
    transcript.append_message(b"blinded_point", blinded_point.to_bytes());
    transcript.append_message(
      b"tree_root",
      match generators_and_tree.tree.root() {
        Hash::Even(even) => even.to_bytes(),
        Hash::Odd(_) => {
          // TODO: use odd.to_bytes()
          let res = [0u8; 32];
          res
        },
      },
    );

    let (ed25519_commitments, _, ed25519_vector_commitments, ed25519_proof, ed25519_proofs) =
      circuit_c1.prove_with_vector_commitments(&mut OsRng, &mut transcript);
    let (bulletproof25519_commitments, _, bulletproof25519_vector_commitments, bulletproof25519_proof, bulletproof25519_proofs) =
      circuit_c2.prove_with_vector_commitments(&mut OsRng, &mut transcript);

    (
      blinded_point,
      Proof {
        ed25519_commitments,
        ed25519_vector_commitments,
        ed25519_proof,
        ed25519_proofs,
        bulletproof25519_commitments,
        bulletproof25519_vector_commitments,
        bulletproof25519_proof,
        bulletproof25519_proofs,
      },
    )
  }

  pub fn verify(
    generators_and_tree: &GeneratorsAndTree,
    blinded_point: <<Ed25519Tower as CurveCycle>::C1 as Ciphersuite>::G,
    proof: &Proof,
  ) -> bool {
    let mut transcript = RecommendedTranscript::new(b"Monero Curve Trees Proof");

    let mut circuit_c1 = Circuit::new(generators_and_tree.ed25519_generators.per_proof(), false);
    let mut circuit_c2 = Circuit::new(generators_and_tree.bulletproof25519_generators.per_proof(), false);
    membership_gadget::<_, _, Ed25519Tower>(
      &mut OsRng,
      &mut transcript,
      &mut circuit_c1,
      &mut circuit_c2,
      &generators_and_tree.tree,
      None,
      None,
    );

    transcript.append_message(b"blinded_point", blinded_point.to_bytes());
    transcript.append_message(
      b"tree_root",
      match generators_and_tree.tree.root() {
        Hash::Even(even) => even.to_bytes(),
        Hash::Odd(_) => {
          // TODO: use odd.to_bytes()
          let res = [0u8; 32];
          res
        },
      },
    );

    // We need to arrange the points as post-vars
    let mut c1_additional = vec![];
    for (i, commitment) in proof.bulletproof25519_vector_commitments.iter().enumerate() {
      if (i % 2) != 1 {
        continue;
      }
      let coords = Ed25519Tower::c2_coords(*commitment);
      c1_additional.push(coords.0);
      c1_additional.push(coords.1);
    }
    let blinded_point_coords = Ed25519Tower::c1_coords(blinded_point);
    let mut c2_additional = vec![blinded_point_coords.0, blinded_point_coords.1];
    for (i, commitment) in proof.ed25519_vector_commitments.iter().enumerate() {
      if (i % 2) != 1 {
        continue;
      }
      let coords = Ed25519Tower::c1_coords(*commitment);
      c2_additional.push(coords.0);
      c2_additional.push(coords.1);
    }

    // The caller must check the tree root aligns
    if (generators_and_tree.tree.depth() % 2) == 1 {
      assert_eq!(Hash::Odd(*proof.bulletproof25519_vector_commitments.last().unwrap()), generators_and_tree.tree.root());
      c1_additional.pop();
      c1_additional.pop();
    } else {
      assert_eq!(Hash::Even(*proof.ed25519_vector_commitments.last().unwrap()), generators_and_tree.tree.root());
      c2_additional.pop();
      c2_additional.pop();
    }

    // TODO: Review this capacity
    let mut verifier_c1 = BatchVerifier::new(3 * 4);
    let mut verifier_c2 = BatchVerifier::new(3 * 4);

    // TODO: remove clones
    circuit_c1.verification_statement_with_vector_commitments().verify(
      &mut OsRng,
      &mut verifier_c1,
      &mut transcript,
      proof.ed25519_commitments.clone(),
      proof.ed25519_vector_commitments.clone(),
      c1_additional,
      proof.ed25519_proof.clone(),
      proof.ed25519_proofs.clone(),
    );
    circuit_c2.verification_statement_with_vector_commitments().verify(
      &mut OsRng,
      &mut verifier_c2,
      &mut transcript,
      proof.bulletproof25519_commitments.clone(),
      proof.bulletproof25519_vector_commitments.clone(),
      c2_additional,
      proof.bulletproof25519_proof.clone(),
      proof.bulletproof25519_proofs.clone(),
    );

    debug_assert!(verifier_c1.verify_vartime());
    debug_assert!(verifier_c2.verify_vartime());
    verifier_c1.verify_vartime() && verifier_c2.verify_vartime()
  }

  pub fn add_leaves(generators_and_tree: &mut GeneratorsAndTree, leaves: &Vec<<<Ed25519Tower as CurveCycle>::C1 as Ciphersuite>::G>) {
    generators_and_tree.tree.add_leaves(leaves);
  }
}
