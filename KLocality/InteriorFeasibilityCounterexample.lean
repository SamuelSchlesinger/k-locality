import Mathlib

namespace KLocality
namespace InteriorFeasibilityCounterexample

/-- Joint probability table on three binary variables `(X, Y, Z)`. -/
structure Joint3 where
  p000 : ℚ
  p001 : ℚ
  p010 : ℚ
  p011 : ℚ
  p100 : ℚ
  p101 : ℚ
  p110 : ℚ
  p111 : ℚ

/-- Strict positivity on every global assignment (the interior condition on full support). -/
structure StrictlyPositive (p : Joint3) : Prop where
  pos000 : 0 < p.p000
  pos001 : 0 < p.p001
  pos010 : 0 < p.p010
  pos011 : 0 < p.p011
  pos100 : 0 < p.p100
  pos101 : 0 < p.p101
  pos110 : 0 < p.p110
  pos111 : 0 < p.p111

/-- Feasibility for the fixed pairwise marginals used in the paper's counterexample:
`XY` with entries `(9/20, 1/20; 1/20, 9/20)`,
`XZ` with entries `(2/5, 1/10; 1/10, 2/5)`,
`YZ` with entries `(7/20, 3/20; 3/20, 7/20)`. -/
structure FeasiblePairwise (p : Joint3) : Prop where
  nonneg000 : 0 ≤ p.p000
  nonneg001 : 0 ≤ p.p001
  nonneg010 : 0 ≤ p.p010
  nonneg011 : 0 ≤ p.p011
  nonneg100 : 0 ≤ p.p100
  nonneg101 : 0 ≤ p.p101
  nonneg110 : 0 ≤ p.p110
  nonneg111 : 0 ≤ p.p111
  total : p.p000 + p.p001 + p.p010 + p.p011 + p.p100 + p.p101 + p.p110 + p.p111 = 1
  xy00 : p.p000 + p.p001 = (9 / 20 : ℚ)
  xy01 : p.p010 + p.p011 = (1 / 20 : ℚ)
  xy10 : p.p100 + p.p101 = (1 / 20 : ℚ)
  xy11 : p.p110 + p.p111 = (9 / 20 : ℚ)
  xz00 : p.p000 + p.p010 = (2 / 5 : ℚ)
  xz01 : p.p001 + p.p011 = (1 / 10 : ℚ)
  xz10 : p.p100 + p.p110 = (1 / 10 : ℚ)
  xz11 : p.p101 + p.p111 = (2 / 5 : ℚ)
  yz00 : p.p000 + p.p100 = (7 / 20 : ℚ)
  yz01 : p.p001 + p.p101 = (3 / 20 : ℚ)
  yz10 : p.p010 + p.p110 = (3 / 20 : ℚ)
  yz11 : p.p011 + p.p111 = (7 / 20 : ℚ)

/-- Explicit feasible witness: it lies on the boundary (`p011 = p100 = 0`). -/
def boundaryWitness : Joint3 where
  p000 := 7 / 20
  p001 := 1 / 10
  p010 := 1 / 20
  p011 := 0
  p100 := 0
  p101 := 1 / 20
  p110 := 1 / 10
  p111 := 7 / 20

/-- Embed a Boolean value into the rationals for the exposing polynomial below. -/
def bitRat (b : Bool) : ℚ :=
  if b then 1 else 0

/-- The quadratic energy exposing the feasible support face:
`x - x*y - x*z + y*z = (x-y)(x-z)` on Boolean inputs. -/
def quadraticEnergy (x y z : Bool) : ℚ :=
  bitRat x - bitRat x * bitRat y - bitRat x * bitRat z + bitRat y * bitRat z

theorem quadraticEnergy_nonneg (x y z : Bool) :
    0 ≤ quadraticEnergy x y z := by
  cases x <;> cases y <;> cases z <;> norm_num [quadraticEnergy, bitRat]

/-- The energy is positive exactly at the two globally forbidden states. -/
theorem quadraticEnergy_eq_one_iff (x y z : Bool) :
    quadraticEnergy x y z = 1 ↔
      (x = false ∧ y = true ∧ z = true) ∨
      (x = true ∧ y = false ∧ z = false) := by
  cases x <;> cases y <;> cases z <;> norm_num [quadraticEnergy, bitRat]

/-- Expectation of the exposing quadratic energy under a joint table. -/
def energyExpectation (p : Joint3) : ℚ :=
  p.p000 * quadraticEnergy false false false +
    p.p001 * quadraticEnergy false false true +
    p.p010 * quadraticEnergy false true false +
    p.p011 * quadraticEnergy false true true +
    p.p100 * quadraticEnergy true false false +
    p.p101 * quadraticEnergy true false true +
    p.p110 * quadraticEnergy true true false +
    p.p111 * quadraticEnergy true true true

/-- Since the energy is one exactly at `011` and `100` and zero elsewhere, its expectation
is the total mass on the two forbidden states. -/
theorem energyExpectation_eq_forbidden_mass (p : Joint3) :
    energyExpectation p = p.p011 + p.p100 := by
  norm_num [energyExpectation, quadraticEnergy, bitRat]

theorem feasible_boundaryWitness : FeasiblePairwise boundaryWitness := by
  refine
    { nonneg000 := by norm_num [boundaryWitness]
      nonneg001 := by norm_num [boundaryWitness]
      nonneg010 := by norm_num [boundaryWitness]
      nonneg011 := by norm_num [boundaryWitness]
      nonneg100 := by norm_num [boundaryWitness]
      nonneg101 := by norm_num [boundaryWitness]
      nonneg110 := by norm_num [boundaryWitness]
      nonneg111 := by norm_num [boundaryWitness]
      total := by norm_num [boundaryWitness]
      xy00 := by norm_num [boundaryWitness]
      xy01 := by norm_num [boundaryWitness]
      xy10 := by norm_num [boundaryWitness]
      xy11 := by norm_num [boundaryWitness]
      xz00 := by norm_num [boundaryWitness]
      xz01 := by norm_num [boundaryWitness]
      xz10 := by norm_num [boundaryWitness]
      xz11 := by norm_num [boundaryWitness]
      yz00 := by norm_num [boundaryWitness]
      yz01 := by norm_num [boundaryWitness]
      yz10 := by norm_num [boundaryWitness]
      yz11 := by norm_num [boundaryWitness] }

/-- Core obstruction: feasibility does not imply strict positivity on all 8 states. -/
theorem not_strictly_positive_of_feasible {p : Joint3} (hFeas : FeasiblePairwise p) :
    ¬ StrictlyPositive p := by
  intro hPos
  have hp100 : p.p100 = p.p111 - (7 / 20 : ℚ) := by
    linarith [hFeas.xy10, hFeas.xz11]
  have hp011 : p.p011 = (7 / 20 : ℚ) - p.p111 := by
    linarith [hFeas.yz11]
  have hgt : p.p111 > (7 / 20 : ℚ) := by
    linarith [hp100, hPos.pos100]
  have hlt : p.p111 < (7 / 20 : ℚ) := by
    linarith [hp011, hPos.pos011]
  linarith

/-- The prescribed pairwise marginals determine the expectation of the exposing energy:
`E[E] = E[X] - E[XY] - E[XZ] + E[YZ] = 1/2 - 9/20 - 2/5 + 7/20 = 0`. -/
theorem energyExpectation_eq_zero_of_feasible
    {p : Joint3} (hFeas : FeasiblePairwise p) :
    energyExpectation p = 0 := by
  rw [energyExpectation_eq_forbidden_mass]
  have hp100 : p.p100 = p.p111 - (7 / 20 : ℚ) := by
    linarith [hFeas.xy10, hFeas.xz11]
  have hp011 : p.p011 = (7 / 20 : ℚ) - p.p111 := by
    linarith [hFeas.yz11]
  linarith

/-- The pairwise expectations force the exposing quadratic energy to have expectation zero,
so the total mass on the two positive-energy states `011` and `100` vanishes. -/
theorem exposing_energy_expectation_eq_zero_of_feasible
    {p : Joint3} (hFeas : FeasiblePairwise p) :
    p.p011 + p.p100 = 0 := by
  rw [← energyExpectation_eq_forbidden_mass]
  exact energyExpectation_eq_zero_of_feasible hFeas

/-- The ground-state certificate directly forces both excluded states to have zero mass. -/
theorem forbidden_states_zero_of_feasible
    {p : Joint3} (hFeas : FeasiblePairwise p) :
    p.p011 = 0 ∧ p.p100 = 0 := by
  have hsum := exposing_energy_expectation_eq_zero_of_feasible hFeas
  constructor <;> linarith [hFeas.nonneg011, hFeas.nonneg100]

/-- The prescribed pairwise marginals have a unique feasible global table. -/
theorem feasible_eq_boundaryWitness
    {p : Joint3} (hFeas : FeasiblePairwise p) :
    p = boundaryWitness := by
  rcases forbidden_states_zero_of_feasible hFeas with ⟨hp011, hp100⟩
  have hp111 : p.p111 = (7 / 20 : ℚ) := by
    linarith [hFeas.yz11]
  have hp110 : p.p110 = (1 / 10 : ℚ) := by
    linarith [hFeas.xy11]
  have hp101 : p.p101 = (1 / 20 : ℚ) := by
    linarith [hFeas.xz11]
  have hp010 : p.p010 = (1 / 20 : ℚ) := by
    linarith [hFeas.yz10]
  have hp001 : p.p001 = (1 / 10 : ℚ) := by
    linarith [hFeas.xz01]
  have hp000 : p.p000 = (7 / 20 : ℚ) := by
    linarith [hFeas.xy00]
  rcases p with ⟨p000, p001, p010, p011, p100, p101, p110, p111⟩
  simp_all [boundaryWitness]

/-- Counterexample package: feasible pairwise marginals exist, but no interior feasible joint exists. -/
theorem exists_feasible_but_no_interior :
    (∃ p : Joint3, FeasiblePairwise p) ∧
      ¬ ∃ p : Joint3, FeasiblePairwise p ∧ StrictlyPositive p := by
  refine ⟨⟨boundaryWitness, feasible_boundaryWitness⟩, ?_⟩
  intro h
  rcases h with ⟨p, hFeas, hPos⟩
  exact (not_strictly_positive_of_feasible hFeas) hPos

/-- All constrained local-pattern probabilities are strictly positive constants. -/
theorem local_targets_are_positive :
    0 < (9 / 20 : ℚ) ∧ 0 < (1 / 20 : ℚ) ∧ 0 < (2 / 5 : ℚ) ∧
      0 < (1 / 10 : ℚ) ∧ 0 < (7 / 20 : ℚ) ∧ 0 < (3 / 20 : ℚ) := by
  norm_num

end InteriorFeasibilityCounterexample
end KLocality
