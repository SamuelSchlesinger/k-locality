import KLocality.Core
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Local energies and uniform ground-state laws

This module proves the constructive direction of the ground-state description needed by
quadratic NAND synthesis.  An energy is presented as a finite sum of functions, each of
which depends on a declared finite scope.  If every scope has size at most `k`, the energy
is nonnegative, and its zero set is a nonempty finite target, then the uniform law on that
target is `k`-local.

Unlike `MarginalLocalCompleteness`, this certificate can use cancellation among several
unary and pairwise terms.  That distinction is essential for the quadratic NAND penalty.
-/

/-- Expected value of a real function under a finite PMF. -/
noncomputable def pmfExpectation
    {α : Type*} [Fintype α] (p : Distribution α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

theorem pmfExpectation_map
    {α β : Type*} [Fintype α] [Fintype β]
    (p : Distribution α) (g : α → β) (f : β → ℝ) :
    pmfExpectation (p.map g) f = pmfExpectation p (fun a => f (g a)) := by
  classical
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSingletonClass α := ⟨fun _ => by trivial⟩
  letI : MeasurableSingletonClass β := ⟨fun _ => by trivial⟩
  have hg : Measurable g := measurable_of_finite _
  have hf : MeasureTheory.StronglyMeasurable f :=
    (measurable_of_finite f).stronglyMeasurable
  unfold pmfExpectation
  simp_rw [← smul_eq_mul]
  rw [← PMF.integral_eq_sum, ← PMF.integral_eq_sum]
  rw [← PMF.toMeasure_map g p hg]
  exact MeasureTheory.integral_map_of_stronglyMeasurable hg hf

@[simp]
theorem pmfExpectation_zero
    {α : Type*} [Fintype α] (p : Distribution α) :
    pmfExpectation p (fun _ => 0) = 0 := by
  simp [pmfExpectation]

theorem pmfExpectation_add
    {α : Type*} [Fintype α] (p : Distribution α) (f g : α → ℝ) :
    pmfExpectation p (fun a => f a + g a) =
      pmfExpectation p f + pmfExpectation p g := by
  simp [pmfExpectation, mul_add, Finset.sum_add_distrib]

/-- Zero expectation of a nonnegative function forces that function to vanish on the PMF support. -/
theorem support_subset_zeroSet_of_pmfExpectation_eq_zero
    {α : Type*} [Fintype α]
    (p : Distribution α) (f : α → ℝ)
    (hNonneg : ∀ a, 0 ≤ f a)
    (hExpectation : pmfExpectation p f = 0) :
    p.support ⊆ {a | f a = 0} := by
  intro a ha
  have hTerms :
      ∀ b ∈ (Finset.univ : Finset α), (p b).toReal * f b = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) ?_).mp
    · simpa [pmfExpectation] using hExpectation
    · intro b _
      exact mul_nonneg ENNReal.toReal_nonneg (hNonneg b)
  have hProduct : (p a).toReal * f a = 0 := hTerms a (Finset.mem_univ a)
  have hpNonzero : p a ≠ 0 := (PMF.mem_support_iff p a).mp ha
  have hpPositive : 0 < (p a).toReal :=
    ENNReal.toReal_pos hpNonzero (p.apply_ne_top a)
  rcases mul_eq_zero.mp hProduct with hpZero | hfZero
  · exact False.elim ((ne_of_gt hpPositive) hpZero)
  · exact Set.mem_setOf_eq.mpr hfZero

/-- A function vanishing on the PMF support has expectation zero. -/
theorem pmfExpectation_eq_zero_of_support_subset_zeroSet
    {α : Type*} [Fintype α]
    (p : Distribution α) (f : α → ℝ)
    (hSupport : p.support ⊆ {a | f a = 0}) :
    pmfExpectation p f = 0 := by
  unfold pmfExpectation
  apply Finset.sum_eq_zero
  intro a _
  by_cases hpa : p a = 0
  · simp [hpa]
  · have ha : a ∈ p.support := (PMF.mem_support_iff p a).mpr hpa
    have hfa : f a = 0 := hSupport ha
    simp [hfa]

/-- One real-valued local energy term together with the scope on which it depends. -/
structure LocalEnergyTerm (Var : Type u) where
  scope : Finset Var
  value : Assignment scope → ℝ

namespace LocalEnergyTerm

/-- Evaluate a scoped term on a global Boolean assignment. -/
def eval
    {Var : Type u}
    (term : LocalEnergyTerm Var) (assignment : Assignment Var) : ℝ :=
  term.value (restrict term.scope assignment)

/-- The marginal constraint canonically attached to a local term and a reference PMF. -/
noncomputable def constraint
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (term : LocalEnergyTerm Var) (p : Distribution (Assignment Var)) :
    MarginalConstraint Var where
  scope := term.scope
  target := marginal term.scope p

theorem pmfExpectation_eval_eq_marginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (term : LocalEnergyTerm Var) (p : Distribution (Assignment Var)) :
    pmfExpectation p term.eval =
      pmfExpectation (marginal term.scope p) term.value := by
  simpa [eval, marginal] using
    (pmfExpectation_map p (restrict term.scope) term.value).symm

end LocalEnergyTerm

/-- Evaluate a finite sum of scoped energy terms. -/
def localEnergyEval
    {Var : Type u}
    (terms : List (LocalEnergyTerm Var)) (assignment : Assignment Var) : ℝ :=
  (terms.map fun term => term.eval assignment).sum

/-- Every term in the energy uses at most `k` variables. -/
def LocalEnergyTermsRespectK
    {Var : Type u}
    (k : Nat) (terms : List (LocalEnergyTerm Var)) : Prop :=
  ∀ term ∈ terms, term.scope.card ≤ k

/-- Canonical marginal constraints fixing the marginal on every energy-term scope. -/
noncomputable def localEnergyConstraints
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (terms : List (LocalEnergyTerm Var))
    (p : Distribution (Assignment Var)) :
    List (MarginalConstraint Var) :=
  terms.map fun term => term.constraint p

theorem localEnergyConstraints_respectK
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {terms : List (LocalEnergyTerm Var)}
    (p : Distribution (Assignment Var))
    (hBound : LocalEnergyTermsRespectK k terms) :
    MarginalConstraintsRespectK k (localEnergyConstraints terms p) := by
  classical
  intro constraint hConstraint
  rcases List.mem_map.mp hConstraint with ⟨term, hTerm, rfl⟩
  exact hBound term hTerm

theorem feasible_localEnergyConstraints_self
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (terms : List (LocalEnergyTerm Var))
    (p : Distribution (Assignment Var)) :
    FeasibleMarginals (localEnergyConstraints terms p) p := by
  classical
  intro constraint hConstraint
  rcases List.mem_map.mp hConstraint with ⟨term, _hTerm, rfl⟩
  rfl

theorem pmfExpectation_localEnergy_eq_sum
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (terms : List (LocalEnergyTerm Var))
    (p : Distribution (Assignment Var)) :
    pmfExpectation p (localEnergyEval terms) =
      (terms.map fun term => pmfExpectation p term.eval).sum := by
  induction terms with
  | nil =>
      rw [show localEnergyEval ([] : List (LocalEnergyTerm Var)) = fun _ => 0 by
        funext assignment
        rfl]
      exact pmfExpectation_zero p
  | cons term terms ih =>
      rw [show localEnergyEval (term :: terms) =
          fun assignment => term.eval assignment + localEnergyEval terms assignment by
        funext assignment
        simp [localEnergyEval]]
      rw [pmfExpectation_add, ih]
      simp

theorem pmfExpectation_term_eq_of_feasible
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {terms : List (LocalEnergyTerm Var)}
    {p q : Distribution (Assignment Var)}
    (hFeasible : FeasibleMarginals (localEnergyConstraints terms p) q)
    {term : LocalEnergyTerm Var} (hTerm : term ∈ terms) :
    pmfExpectation q term.eval = pmfExpectation p term.eval := by
  classical
  have hConstraintMem : term.constraint p ∈ localEnergyConstraints terms p := by
    exact List.mem_map.mpr ⟨term, hTerm, rfl⟩
  have hMarginal : marginal term.scope q = marginal term.scope p :=
    hFeasible (term.constraint p) hConstraintMem
  rw [term.pmfExpectation_eval_eq_marginal, term.pmfExpectation_eval_eq_marginal,
    hMarginal]

theorem pmfExpectation_localEnergy_eq_of_feasible
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {terms : List (LocalEnergyTerm Var)}
    {p q : Distribution (Assignment Var)}
    (hFeasible : FeasibleMarginals (localEnergyConstraints terms p) q) :
    pmfExpectation q (localEnergyEval terms) =
      pmfExpectation p (localEnergyEval terms) := by
  rw [pmfExpectation_localEnergy_eq_sum, pmfExpectation_localEnergy_eq_sum]
  congr 1
  apply List.map_congr_left
  intro term hTerm
  exact pmfExpectation_term_eq_of_feasible hFeasible hTerm

/-- A nonnegative `k`-scope energy makes its uniform ground-state law `k`-local. -/
theorem uniformOn_isKLocalMarginal_of_localEnergy
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat)
    (target : Finset (Assignment Var)) (hTarget : target.Nonempty)
    (terms : List (LocalEnergyTerm Var))
    (hBound : LocalEnergyTermsRespectK k terms)
    (hNonneg : ∀ assignment, 0 ≤ localEnergyEval terms assignment)
    (hGround : ∀ assignment, assignment ∈ target ↔ localEnergyEval terms assignment = 0) :
    IsKLocalMarginal k (uniformOn target hTarget) := by
  let p : Distribution (Assignment Var) := uniformOn target hTarget
  refine ⟨localEnergyConstraints terms p,
    localEnergyConstraints_respectK p hBound, ?_⟩
  refine ⟨feasible_localEnergyConstraints_self terms p, ?_⟩
  intro q hq
  have hpSupportZero : p.support ⊆ {assignment | localEnergyEval terms assignment = 0} := by
    intro assignment hAssignment
    have hInTarget : assignment ∈ target := by
      simpa [p] using hAssignment
    exact hGround assignment |>.mp hInTarget
  have hpExpectationZero : pmfExpectation p (localEnergyEval terms) = 0 :=
    pmfExpectation_eq_zero_of_support_subset_zeroSet p (localEnergyEval terms) hpSupportZero
  have hqExpectationZero : pmfExpectation q (localEnergyEval terms) = 0 := by
    rw [pmfExpectation_localEnergy_eq_of_feasible hq]
    exact hpExpectationZero
  have hqSupportZero : q.support ⊆ {assignment | localEnergyEval terms assignment = 0} :=
    support_subset_zeroSet_of_pmfExpectation_eq_zero q (localEnergyEval terms) hNonneg
      hqExpectationZero
  have hqSupportTarget : q.support ⊆ (target : Set (Assignment Var)) := by
    intro assignment hAssignment
    exact hGround assignment |>.mpr (hqSupportZero hAssignment)
  have hEntropyBound :=
    shannonEntropy_le_log_card_of_support_subset q target hTarget hqSupportTarget
  have hUniformEntropy := shannonEntropy_uniformOn target hTarget
  simpa [p, hUniformEntropy] using hEntropyBound

/-- Package a local-energy ground space whose observed marginal is known into a localization. -/
noncomputable def kLocalizationOfLocalEnergyGroundStates
    {k : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [DecidableEq ObsVar] [Fintype ObsVar]
    [DecidableEq LatVar] [Fintype LatVar]
    {pObs : Distribution (Assignment ObsVar)}
    (target : Finset (Assignment (Sum ObsVar LatVar)))
    (hTarget : target.Nonempty)
    (terms : List (LocalEnergyTerm (Sum ObsVar LatVar)))
    (hBound : LocalEnergyTermsRespectK k terms)
    (hNonneg : ∀ assignment, 0 ≤ localEnergyEval terms assignment)
    (hGround : ∀ assignment,
      assignment ∈ target ↔ localEnergyEval terms assignment = 0)
    (hMarginal : IsMarginalModel pObs (uniformOn target hTarget)) :
    KLocalization k ObsVar LatVar pObs :=
  { lifted := uniformOn target hTarget
    marginal := hMarginal
    kLocal := uniformOn_isKLocalMarginal_of_localEnergy
      k target hTarget terms hBound hNonneg hGround }

/-- Bit-vector specialization of `kLocalizationOfLocalEnergyGroundStates`. -/
theorem hasKLocalizationBits_of_localEnergyGroundStates
    {k n latentBits : Nat}
    {pObs : Distribution (BitVec n)}
    (target : Finset (Assignment (Sum (Fin n) (Fin latentBits))))
    (hTarget : target.Nonempty)
    (terms : List (LocalEnergyTerm (Sum (Fin n) (Fin latentBits))))
    (hBound : LocalEnergyTermsRespectK k terms)
    (hNonneg : ∀ assignment, 0 ≤ localEnergyEval terms assignment)
    (hGround : ∀ assignment,
      assignment ∈ target ↔ localEnergyEval terms assignment = 0)
    (hMarginal : IsMarginalModel pObs (uniformOn target hTarget)) :
    HasKLocalizationBits k latentBits n pObs := by
  exact ⟨kLocalizationOfLocalEnergyGroundStates target hTarget terms
    hBound hNonneg hGround hMarginal⟩

end KLocality
