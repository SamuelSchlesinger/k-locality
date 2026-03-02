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
