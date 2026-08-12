import KLocality.FacialSupport
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace KLocality

open scoped BigOperators
open Filter Topology

universe u

/-!
# Entropy optimality and log-density coordinates

This file proves the first-order-optimality half of the forward implication in
Theorem `thm:face-gibbs`.  A tangent direction in the canonical moment fiber
which vanishes off the support can be followed in both signs while remaining
inside the probability simplex.  Entropy maximality therefore makes the
support log-density annihilate every such direction.  Finite-dimensional
duality then expresses that log-density as a degree-`k` feature polynomial on
the support.
-/

/-- Coordinate evaluation, masked to vanish identically on coordinates in the
support.  These maps encode the condition that tangent directions do not turn
on new support points. -/
noncomputable def outsideCoordinateFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) (x : Assignment Var) :
    (Assignment Var → ℝ) →ₗ[ℝ] ℝ := by
  classical
  exact if x ∈ p.support then 0 else LinearMap.proj x

@[simp]
theorem outsideCoordinateFunctional_apply_of_mem
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) (x : Assignment Var)
    (weights : Assignment Var → ℝ) (hx : x ∈ p.support) :
    outsideCoordinateFunctional p x weights = 0 := by
  classical
  simp [outsideCoordinateFunctional, hx]

@[simp]
theorem outsideCoordinateFunctional_apply_of_not_mem
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) (x : Assignment Var)
    (weights : Assignment Var → ℝ) (hx : x ∉ p.support) :
    outsideCoordinateFunctional p x weights = weights x := by
  classical
  simp [outsideCoordinateFunctional, hx, LinearMap.proj_apply]

/-- The combined linear constraints for tangent directions: canonical moments
on the left summand and vanishing outside the support on the right. -/
noncomputable def supportTangentFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    Sum (FeatureScope Var k) (Assignment Var) →
      ((Assignment Var → ℝ) →ₗ[ℝ] ℝ)
  | Sum.inl scope => FeaturePolynomial.momentFunctional scope
  | Sum.inr x => outsideCoordinateFunctional p x

@[simp]
theorem supportTangentFunctional_inl
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (scope : FeatureScope Var k) :
    supportTangentFunctional k p (Sum.inl scope) =
      FeaturePolynomial.momentFunctional scope :=
  rfl

@[simp]
theorem supportTangentFunctional_inr
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (x : Assignment Var) :
    supportTangentFunctional k p (Sum.inr x) =
      outsideCoordinateFunctional p x :=
  rfl

/-- The log-density paired with a real tangent table, extended by zero away
from the support. -/
noncomputable def supportLogFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) :
    (Assignment Var → ℝ) →ₗ[ℝ] ℝ where
  toFun direction :=
    ∑ x ∈ UniversalExistence.supportFinset p,
      direction x * Real.log (p x).toReal
  map_add' left right := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar direction := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

@[simp]
theorem supportLogFunctional_apply
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ) :
    supportLogFunctional p direction =
      ∑ x ∈ UniversalExistence.supportFinset p,
        direction x * Real.log (p x).toReal :=
  rfl

/-- Entropy along the affine real-weight line through `p`. -/
noncomputable def entropyAlong
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ) (t : ℝ) : ℝ :=
  ∑ x, Real.negMulLog ((p x).toReal + t * direction x)

/-- Nonnegativity at one positive endpoint implies nonnegativity all along
the segment from the nonnegative base table to that endpoint. -/
theorem affine_nonnegative_between
    {α : Type u} [Fintype α]
    (base direction : α → ℝ)
    (hBase : ∀ i, 0 ≤ base i)
    {epsilon t : ℝ} (hEndpoint : ∀ i, 0 ≤ base i + epsilon * direction i)
    (ht : 0 ≤ t) (htEpsilon : t ≤ epsilon) :
    ∀ i, 0 ≤ base i + t * direction i := by
  intro i
  by_cases hDirection : 0 ≤ direction i
  · exact add_nonneg (hBase i) (mul_nonneg ht hDirection)
  · have hMul : epsilon * direction i ≤ t * direction i :=
      mul_le_mul_of_nonpos_right htEpsilon (le_of_not_ge hDirection)
    linarith [hEndpoint i]

/-- An affine tangent table with zero total mass still has total mass one. -/
theorem sum_affine_realWeights_eq_one
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ)
    (hDirectionSum : ∑ x, direction x = 0) (t : ℝ) :
    ∑ x, ((p x).toReal + t * direction x) = 1 := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hDirectionSum, mul_zero, add_zero]
  exact sum_toReal_eq_one_of_support_subset p Finset.univ (by simp)

/-- Turning a nonnegative affine tangent table into a PMF preserves every
canonical feature moment when the direction lies in the moment-map kernel. -/
theorem sameFeatureMoments_distributionOfRealWeights_affine
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ)
    (hKernel : direction ∈ LinearMap.ker (FeaturePolynomial.momentMap k))
    (t : ℝ)
    (hNonneg : ∀ x, 0 ≤ (p x).toReal + t * direction x) :
    SameFeatureMomentsUpTo k p
      (distributionOfRealWeights
        (fun x => (p x).toReal + t * direction x) hNonneg
        (sum_affine_realWeights_eq_one p direction
          (sum_direction_eq_zero_of_mem_momentMap_ker hKernel) t)) := by
  classical
  apply (FeaturePolynomial.sameFeatureMomentsUpTo_iff_momentMap_realWeights_eq
    k p _).2
  funext scope
  rw [FeaturePolynomial.momentMap_apply, FeaturePolynomial.momentMap_apply]
  simp_rw [FeaturePolynomial.realWeights,
    distributionOfRealWeights_apply_toReal]
  simp only [add_mul, Finset.sum_add_distrib]
  have hScopeZero := congrFun hKernel scope
  have hDirectionMoment :
      ∑ x, direction x * monomialValue scope.1 x = 0 := by
    simpa [FeaturePolynomial.momentMap_apply] using hScopeZero
  have hFactor :
      (∑ x, t * direction x * monomialValue scope.1 x) =
        t * ∑ x, direction x * monomialValue scope.1 x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hFactor, hDirectionMoment, mul_zero, add_zero]

/-- The affine entropy path is the Shannon entropy of the PMF built from its
weights whenever those weights are nonnegative. -/
theorem entropyAlong_eq_shannonEntropy_distributionOfRealWeights
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ) (t : ℝ)
    (hNonneg : ∀ x, 0 ≤ (p x).toReal + t * direction x)
    (hDirectionSum : ∑ x, direction x = 0) :
    entropyAlong p direction t =
      shannonEntropy
        (distributionOfRealWeights
          (fun x => (p x).toReal + t * direction x) hNonneg
          (sum_affine_realWeights_eq_one p direction hDirectionSum t)) := by
  classical
  unfold entropyAlong shannonEntropy
  apply Finset.sum_congr rfl
  intro x _
  rw [distributionOfRealWeights_apply_toReal]

@[simp]
theorem entropyAlong_zero
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ) :
    entropyAlong p direction 0 = shannonEntropy p := by
  simp [entropyAlong, shannonEntropy]

/-- The derivative of entropy along a support-preserving affine line. -/
theorem hasDerivAt_entropyAlong
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ)
    (hOutside : ∀ x, x ∉ p.support → direction x = 0) :
    HasDerivAt (entropyAlong p direction)
      (∑ x, (-Real.log (p x).toReal - 1) * direction x) 0 := by
  classical
  unfold entropyAlong
  apply HasDerivAt.fun_sum
  intro x _
  by_cases hx : x ∈ p.support
  · have hpPos : 0 < (p x).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff p x).1 hx) (p.apply_ne_top x)
    have hAffine : HasDerivAt
        (fun t : ℝ => (p x).toReal + t * direction x) (direction x) 0 := by
      simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (direction x)).const_add
        (p x).toReal
    have hOuter : HasDerivAt Real.negMulLog
        (-Real.log (p x).toReal - 1)
        ((p x).toReal + (0 : ℝ) * direction x) := by
      simpa using Real.hasDerivAt_negMulLog hpPos.ne'
    simpa [Function.comp_def] using hOuter.comp 0 hAffine
  · have hpZero : p x = 0 := (p.apply_eq_zero_iff x).2 hx
    have hDirectionZero : direction x = 0 := hOutside x hx
    simpa [hpZero, hDirectionZero] using
      (hasDerivAt_const (𝕜 := ℝ) (x := (0 : ℝ)) (0 : ℝ))

/-- Entropy maximality makes the support log-density orthogonal to every
support-preserving tangent direction in the canonical moment fiber. -/
theorem supportLogFunctional_eq_zero_of_isKLocalMarginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hLocal : IsKLocalMarginal k p)
    (direction : Assignment Var → ℝ)
    (hKernel : direction ∈ LinearMap.ker (FeaturePolynomial.momentMap k))
    (hOutside : ∀ x, x ∉ p.support → direction x = 0) :
    supportLogFunctional p direction = 0 := by
  classical
  let base := FeaturePolynomial.realWeights p
  have hBase : ∀ x, 0 ≤ base x := fun _ => ENNReal.toReal_nonneg
  have hAtZero : ∀ x, base x = 0 → direction x = 0 := by
    intro x hx
    have hpZero : p x = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (p x)).1 hx with hpZero | hpTop
      · exact hpZero
      · exact False.elim ((p.apply_ne_top x) hpTop)
    exact hOutside x ((p.apply_eq_zero_iff x).1 hpZero)
  rcases exists_positive_perturbation_nonnegative base direction hBase
      (fun x hx => (hAtZero x hx).ge) with
    ⟨epsilonPlus, hEpsilonPlus, hPlus⟩
  rcases exists_positive_perturbation_nonnegative base (-direction) hBase
      (fun x hx => by simp [hAtZero x hx]) with
    ⟨epsilonMinus, hEpsilonMinus, hMinus⟩
  let delta := min epsilonPlus epsilonMinus
  have hDelta : 0 < delta := lt_min hEpsilonPlus hEpsilonMinus
  have hDirectionSum : ∑ x, direction x = 0 :=
    sum_direction_eq_zero_of_mem_momentMap_ker hKernel
  have hLocalMax : IsLocalMax (entropyAlong p direction) 0 := by
    show ∀ᶠ t in 𝓝 (0 : ℝ), entropyAlong p direction t ≤ entropyAlong p direction 0
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hDelta] with t ht
    have hAbs : |t| < delta := by
      simpa [Real.dist_eq] using ht
    have hNonneg : ∀ x, 0 ≤ (p x).toReal + t * direction x := by
      by_cases htNonneg : 0 ≤ t
      · have htDelta : t < delta := by
          simpa [abs_of_nonneg htNonneg] using hAbs
        have htPlus : t ≤ epsilonPlus :=
          le_trans htDelta.le (min_le_left _ _)
        simpa [base, FeaturePolynomial.realWeights] using
          affine_nonnegative_between base direction hBase hPlus htNonneg htPlus
      · have htNeg : t < 0 := lt_of_not_ge htNonneg
        have hNegTNonneg : 0 ≤ -t := neg_nonneg.mpr htNeg.le
        have hNegTLe : -t ≤ epsilonMinus := by
          have hAbsEq : |t| = -t := abs_of_neg htNeg
          rw [← hAbsEq]
          exact le_trans (le_of_lt hAbs) (min_le_right _ _)
        have hForNeg := affine_nonnegative_between base (-direction) hBase hMinus
          hNegTNonneg hNegTLe
        intro x
        simpa [base, FeaturePolynomial.realWeights] using hForNeg x
    let q := distributionOfRealWeights
      (fun x => (p x).toReal + t * direction x) hNonneg
      (sum_affine_realWeights_eq_one p direction hDirectionSum t)
    have hMoments : SameFeatureMomentsUpTo k p q := by
      exact sameFeatureMoments_distributionOfRealWeights_affine p direction hKernel t hNonneg
    have hMax := (isKLocalMarginal_iff_maxEntropy_sameFeatureMoments k p).1 hLocal
    have hEntropyLe : shannonEntropy q ≤ shannonEntropy p := hMax.2 q hMoments
    rw [entropyAlong_eq_shannonEntropy_distributionOfRealWeights
      p direction t hNonneg hDirectionSum, entropyAlong_zero]
    exact hEntropyLe
  have hDerivativeZero := hLocalMax.hasDerivAt_eq_zero
    (hasDerivAt_entropyAlong p direction hOutside)
  have hSupportDerivative :
      (∑ x, (-Real.log (p x).toReal - 1) * direction x) =
        -supportLogFunctional p direction := by
    rw [supportLogFunctional_apply]
    let support := UniversalExistence.supportFinset p
    have hRestrict :
        (∑ x, (-Real.log (p x).toReal - 1) * direction x) =
          ∑ x ∈ support,
            (-Real.log (p x).toReal - 1) * direction x := by
      symm
      apply Finset.sum_subset (by intro x _; simp)
      intro x _ hxNot
      have hxOutside : x ∉ p.support := by
        intro hxSupport
        exact hxNot ((UniversalExistence.mem_supportFinset p x).2 hxSupport)
      simp [hOutside x hxOutside]
    rw [hRestrict]
    calc
      (∑ x ∈ support,
          (-Real.log (p x).toReal - 1) * direction x) =
          ∑ x ∈ support,
            (-(direction x * Real.log (p x).toReal) - direction x) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = -(∑ x ∈ support, direction x * Real.log (p x).toReal) -
            ∑ x ∈ support, direction x := by
              rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      _ = -(∑ x ∈ support, direction x * Real.log (p x).toReal) := by
        have hDirectionSupport : ∑ x ∈ support, direction x = 0 := by
          calc
            ∑ x ∈ support, direction x = ∑ x, direction x := by
              apply Finset.sum_subset (by intro x _; simp)
              intro x _ hxNot
              have hxOutside : x ∉ p.support := by
                intro hxSupport
                exact hxNot ((UniversalExistence.mem_supportFinset p x).2 hxSupport)
              exact hOutside x hxOutside
            _ = 0 := hDirectionSum
        rw [hDirectionSupport, sub_zero]
  rw [hSupportDerivative] at hDerivativeZero
  exact neg_eq_zero.mp hDerivativeZero

/-- A direction lying in every combined tangent-functional kernel has zero
support log pairing. -/
theorem supportTangent_iInf_ker_le_supportLog_ker
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hLocal : IsKLocalMarginal k p) :
    (⨅ i, LinearMap.ker (supportTangentFunctional k p i)) ≤
      LinearMap.ker (supportLogFunctional p) := by
  intro direction hDirection
  have hKernel : direction ∈ LinearMap.ker
      (FeaturePolynomial.momentMap k) := by
    change FeaturePolynomial.momentMap k direction = 0
    funext scope
    exact (Submodule.mem_iInf _).1 hDirection (Sum.inl scope)
  have hOutside : ∀ x, x ∉ p.support → direction x = 0 := by
    intro x hx
    have hAtX := (Submodule.mem_iInf _).1 hDirection (Sum.inr x)
    change outsideCoordinateFunctional p x direction = 0 at hAtX
    rw [outsideCoordinateFunctional_apply_of_not_mem p x direction hx] at hAtX
    exact hAtX
  exact supportLogFunctional_eq_zero_of_isKLocalMarginal
    k p hLocal direction hKernel hOutside

/-- The log-density of a `k`-local law is a degree-`k` feature polynomial on
its positive support. -/
theorem isFeatureGibbs_of_isKLocalMarginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hLocal : IsKLocalMarginal k p) :
    IsFeatureGibbs k p := by
  classical
  have hSpan : supportLogFunctional p ∈ Submodule.span ℝ
      (Set.range (supportTangentFunctional k p)) :=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker
      (supportTangent_iInf_ker_le_supportLog_ker k p hLocal)
  rcases (Submodule.mem_span_range_iff_exists_fun ℝ).1 hSpan with
    ⟨coefficients, hCoefficients⟩
  let theta : FeaturePolynomial Var k := fun scope => coefficients (Sum.inl scope)
  refine ⟨theta, ?_⟩
  intro x hx
  let pointMass : Assignment Var → ℝ := Pi.single x 1
  have hAtX := LinearMap.congr_fun hCoefficients pointMass
  have hLogSingle : supportLogFunctional p pointMass =
      Real.log (p x).toReal := by
    rw [supportLogFunctional_apply]
    have hxFinset : x ∈ UniversalExistence.supportFinset p :=
      (UniversalExistence.mem_supportFinset p x).2 hx
    rw [← Finset.sum_erase_add _ _ hxFinset]
    have hOff : ∑ y ∈ (UniversalExistence.supportFinset p).erase x,
        pointMass y * Real.log (p y).toReal = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hyNe : y ≠ x := (Finset.mem_erase.mp hy).1
      simp [pointMass, Pi.single_eq_of_ne hyNe]
    rw [hOff, zero_add]
    simp [pointMass]
  have hOutsideSum :
      (∑ y : Assignment Var,
        coefficients (Sum.inr y) •
          outsideCoordinateFunctional p y pointMass) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y ∈ p.support
    · change coefficients (Sum.inr y) *
          outsideCoordinateFunctional p y pointMass = 0
      rw [outsideCoordinateFunctional_apply_of_mem p y pointMass hy]
      ring
    · have hyNe : y ≠ x := by
        intro hyx
        exact hy (hyx ▸ hx)
      change coefficients (Sum.inr y) *
          outsideCoordinateFunctional p y pointMass = 0
      rw [outsideCoordinateFunctional_apply_of_not_mem p y pointMass hy]
      have hPointMassZero : pointMass y = 0 := by
        simp [pointMass, hyNe]
      rw [hPointMassZero, mul_zero]
  have hMomentPoint : ∀ scope : FeatureScope Var k,
      FeaturePolynomial.momentFunctional scope pointMass =
        monomialValue scope.1 x := by
    intro scope
    change FeaturePolynomial.momentFunctional scope (Pi.single x 1) =
      monomialValue scope.1 x
    exact FeaturePolynomial.momentFunctional_single scope x
  calc
    Real.log (p x).toReal = supportLogFunctional p pointMass := hLogSingle.symm
    _ = (∑ i, coefficients i • supportTangentFunctional k p i) pointMass := by
      rw [hCoefficients]
    _ = (∑ scope : FeatureScope Var k,
          coefficients (Sum.inl scope) * monomialValue scope.1 x) +
          ∑ y : Assignment Var,
            coefficients (Sum.inr y) •
              outsideCoordinateFunctional p y pointMass := by
      rw [Fintype.sum_sum_type, LinearMap.add_apply]
      simp_rw [LinearMap.sum_apply, supportTangentFunctional_inl,
        supportTangentFunctional_inr, LinearMap.smul_apply, smul_eq_mul,
        hMomentPoint]
    _ = ∑ scope : FeatureScope Var k,
          coefficients (Sum.inl scope) * monomialValue scope.1 x := by
      rw [hOutsideSum, add_zero]
    _ = theta.eval x := rfl

/-- **Theorem `thm:face-gibbs`, certificate form.** A finite Boolean law is
`k`-local exactly when its support is exposed by a nonnegative degree-`k`
polynomial and its log-density on that support is degree `k`. -/
theorem isKLocalMarginal_iff_isFaceGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    IsKLocalMarginal k p ↔ IsFaceGibbs k p := by
  constructor
  · intro hLocal
    exact ⟨isFacialSupport_of_isKLocalMarginal k p hLocal,
      isFeatureGibbs_of_isKLocalMarginal k p hLocal⟩
  · exact isKLocalMarginal_of_isFaceGibbs k p

end KLocality
