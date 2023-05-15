use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  PointVector,
  arithmetic_circuit::{Commitment, Constraint, Circuit},
};

type Generators =
  (PointVector<Ristretto>, PointVector<Ristretto>, PointVector<Ristretto>, PointVector<Ristretto>);

fn generators(n: usize) -> Generators {
  let gens = || {
    let mut res = PointVector::<Ristretto>::new(n);
    for i in 0 .. n {
      res[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
    }
    res
  };
  (gens(), gens(), gens(), gens())
}

#[test]
fn test_arithmetic_circuit() {
  let (g_bold1, g_bold2, h_bold1, h_bold2) = generators(128);

  // Basic circuit for:
  // Commitmnts x, y, z, z1
  // x * y = z
  // z + 1 = z1

  fn gadget(
    circuit: &mut Circuit<Ristretto>,
    x_y_z_z1: Option<(
      Commitment<Ristretto>,
      Commitment<Ristretto>,
      Commitment<Ristretto>,
      Commitment<Ristretto>,
    )>,
    commitments: (
      <Ristretto as Ciphersuite>::G,
      <Ristretto as Ciphersuite>::G,
      <Ristretto as Ciphersuite>::G,
      <Ristretto as Ciphersuite>::G,
    ),
  ) {
    let x_var = circuit.add_secret_input(x_y_z_z1.as_ref().map(|xyz| xyz.0.value));
    let x_com =
      circuit.add_committed_input(x_y_z_z1.as_ref().map(|xyz| xyz.0.clone()), commitments.0);

    let y_var = circuit.add_secret_input(x_y_z_z1.as_ref().map(|xyz| xyz.1.value));
    let y_com =
      circuit.add_committed_input(x_y_z_z1.as_ref().map(|xyz| xyz.1.clone()), commitments.1);

    let z_com =
      circuit.add_committed_input(x_y_z_z1.as_ref().map(|xyz| xyz.2.clone()), commitments.2);

    let z1_com =
      circuit.add_committed_input(x_y_z_z1.as_ref().map(|xyz| xyz.3.clone()), commitments.3);

    let product = circuit.product(x_var, y_var);

    let mut next_constraint = Constraint::new();
    next_constraint
      .weight_left(product, <Ristretto as Ciphersuite>::F::ONE)
      .weight_commitment(x_com, <Ristretto as Ciphersuite>::F::ONE);
    circuit.constrain(next_constraint);

    let mut next_constraint = Constraint::new();
    next_constraint
      .weight_right(product, <Ristretto as Ciphersuite>::F::ONE)
      .weight_commitment(y_com, <Ristretto as Ciphersuite>::F::ONE);
    circuit.constrain(next_constraint);

    let mut next_constraint = Constraint::new();
    next_constraint
      .weight_output(product, <Ristretto as Ciphersuite>::F::ONE)
      .weight_commitment(z_com, <Ristretto as Ciphersuite>::F::ONE);
    circuit.constrain(next_constraint);

    let mut next_constraint = Constraint::new();
    next_constraint
      .weight_output(product, <Ristretto as Ciphersuite>::F::ONE)
      .weight_commitment(z1_com, <Ristretto as Ciphersuite>::F::ONE)
      .offset(<Ristretto as Ciphersuite>::F::ONE);
    circuit.constrain(next_constraint);
  }

  let x = Commitment::masking(&mut OsRng, <Ristretto as Ciphersuite>::F::random(&mut OsRng));
  let y = Commitment::masking(&mut OsRng, <Ristretto as Ciphersuite>::F::random(&mut OsRng));
  let z = Commitment::masking(&mut OsRng, x.value * y.value);
  let z1 = Commitment::masking(&mut OsRng, z.value + <Ristretto as Ciphersuite>::F::ONE);

  let mut transcript = RecommendedTranscript::new(b"Arithmetic Circuit Test");

  let mut circuit =
    Circuit::new(g_bold1.clone(), g_bold2.clone(), h_bold1.clone(), h_bold2.clone(), true);
  gadget(
    &mut circuit,
    Some((x.clone(), y.clone(), z.clone(), z1.clone())),
    (x.calculate(), y.calculate(), z.calculate(), z1.calculate()),
  );
  let proof = circuit.prove(&mut OsRng, &mut transcript.clone());

  let mut circuit = Circuit::new(g_bold1, g_bold2, h_bold1, h_bold2, false);
  gadget(&mut circuit, None, (x.calculate(), y.calculate(), z.calculate(), z1.calculate()));
  circuit.verify(&mut transcript, proof);
}
