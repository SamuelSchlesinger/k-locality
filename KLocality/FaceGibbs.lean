import KLocality.FeaturePolynomial

namespace KLocality

open scoped BigOperators

universe u

/-!
# Face--Gibbs laws

This file develops the analytic half of Theorem `thm:face-gibbs`.  It proves
that a nonnegative degree-`k` exposing energy together with a degree-`k`
log-density makes the law the entropy maximizer in its canonical moment
fiber.  The converse construction is developed separately from finite
polyhedral separation and first-order optimality.
-/

/-- The tangent-line inequality for `-x log x` at a positive point. -/
theorem negMulLog_le_tangent
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤
      Real.negMulLog y + (-Real.log y - 1) * (x - y) := by
  have hz : 0 ≤ x / y := div_nonneg hx hy.le
  have hBasic := negMulLog_le_one_sub (x / y) hz
  have hxy : y * (x / y) = x := by field_simp
  calc
    Real.negMulLog x = Real.negMulLog (y * (x / y)) := by rw [hxy]
    _ = (x / y) * Real.negMulLog y +
        y * Real.negMulLog (x / y) := Real.negMulLog_mul y (x / y)
    _ ≤ (x / y) * Real.negMulLog y + y * (1 - x / y) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hBasic hy.le) _
    _ = Real.negMulLog y + (-Real.log y - 1) * (x - y) := by
      rw [show Real.negMulLog y = -y * Real.log y by rfl]
      field_simp
      ring

/-- Restrict a finite expectation to any finset containing the PMF support. -/
theorem pmfExpectation_eq_sum_on_finset_of_support_subset
    {α : Type u} [Fintype α]
    (p : Distribution α) (s : Finset α) (f : α → ℝ)
    (hSupport : p.support ⊆ (s : Set α)) :
    pmfExpectation p f = ∑ x ∈ s, (p x).toReal * f x := by
  classical
  unfold pmfExpectation
  symm
  apply Finset.sum_subset (by intro x _; simp)
  intro x _ hxNot
  have hxZero : p x = 0 := (p.apply_eq_zero_iff x).2 fun hxSupport =>
    hxNot (hSupport hxSupport)
  simp [hxZero]

theorem sameFeatureMoments_support_subset_of_facial
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p q : Distribution (Assignment Var)}
    (hFacial : IsFacialSupport k p.support)
    (hMoments : SameFeatureMomentsUpTo k p q) :
    q.support ⊆ p.support := by
  rcases hFacial with ⟨energy, hNonneg, hZero⟩
  have hpZero : p.support ⊆ {x | energy.eval x = 0} := by
    intro x hx
    exact (hZero x).2 hx
  have hpExpectation : pmfExpectation p energy.eval = 0 :=
    pmfExpectation_eq_zero_of_support_subset_zeroSet p energy.eval hpZero
  have hqExpectation : pmfExpectation q energy.eval = 0 := by
    rw [energy.expectation_eval_eq_of_sameFeatureMoments hMoments]
    exact hpExpectation
  have hqZero := support_subset_zeroSet_of_pmfExpectation_eq_zero
    q energy.eval hNonneg hqExpectation
  intro x hx
  exact (hZero x).1 (hqZero hx)

theorem shannonEntropy_le_of_sameFeatureMoments_faceGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p q : Distribution (Assignment Var)}
    (hFaceGibbs : IsFaceGibbs k p)
    (hMoments : SameFeatureMomentsUpTo k p q) :
    shannonEntropy q ≤ shannonEntropy p := by
  classical
  rcases hFaceGibbs with ⟨hFacial, theta, hLog⟩
  let support := UniversalExistence.supportFinset p
  have hpSupport : p.support ⊆ (support : Set (Assignment Var)) := by
    intro x hx
    exact (UniversalExistence.mem_supportFinset p x).2 hx
  have hqSupportP : q.support ⊆ p.support :=
    sameFeatureMoments_support_subset_of_facial hFacial hMoments
  have hqSupport : q.support ⊆ (support : Set (Assignment Var)) :=
    Set.Subset.trans hqSupportP hpSupport
  have hMassP : ∑ x ∈ support, (p x).toReal = 1 :=
    sum_toReal_eq_one_of_support_subset p support hpSupport
  have hMassQ : ∑ x ∈ support, (q x).toReal = 1 :=
    sum_toReal_eq_one_of_support_subset q support hqSupport
  have hExpectation :=
    theta.expectation_eval_eq_of_sameFeatureMoments hMoments
  rw [pmfExpectation_eq_sum_on_finset_of_support_subset q support theta.eval hqSupport,
    pmfExpectation_eq_sum_on_finset_of_support_subset p support theta.eval hpSupport]
      at hExpectation
  have hPointwise : ∀ x ∈ support,
      Real.negMulLog (q x).toReal ≤
        Real.negMulLog (p x).toReal +
          (-Real.log (p x).toReal - 1) * ((q x).toReal - (p x).toReal) := by
    intro x hx
    have hxSupport : x ∈ p.support :=
      (UniversalExistence.mem_supportFinset p x).1 hx
    have hpPos : 0 < (p x).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff p x).1 hxSupport) (p.apply_ne_top x)
    exact negMulLog_le_tangent ENNReal.toReal_nonneg hpPos
  have hTangentSum := Finset.sum_le_sum hPointwise
  have hCorrection :
      (∑ x ∈ support,
        (-Real.log (p x).toReal - 1) * ((q x).toReal - (p x).toReal)) = 0 := by
    calc
      _ = ∑ x ∈ support,
          (-((q x).toReal * theta.eval x) + (p x).toReal * theta.eval x -
            (q x).toReal + (p x).toReal) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hLog x ((UniversalExistence.mem_supportFinset p x).1 hx)]
            ring
      _ = -(∑ x ∈ support, (q x).toReal * theta.eval x) +
            (∑ x ∈ support, (p x).toReal * theta.eval x) -
            (∑ x ∈ support, (q x).toReal) +
            (∑ x ∈ support, (p x).toReal) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_neg_distrib]
      _ = 0 := by rw [hExpectation, hMassQ, hMassP]; ring
  rw [shannonEntropy_eq_sum_on_finset_of_support_subset q support hqSupport,
    shannonEntropy_eq_sum_on_finset_of_support_subset p support hpSupport]
  calc
    ∑ x ∈ support, Real.negMulLog (q x).toReal ≤
        ∑ x ∈ support,
          (Real.negMulLog (p x).toReal +
            (-Real.log (p x).toReal - 1) *
              ((q x).toReal - (p x).toReal)) := hTangentSum
    _ = ∑ x ∈ support, Real.negMulLog (p x).toReal := by
      rw [Finset.sum_add_distrib, hCorrection, add_zero]

/-- The certificate-form face--Gibbs condition implies `k`-locality. -/
theorem isKLocalMarginal_of_isFaceGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hFaceGibbs : IsFaceGibbs k p) :
    IsKLocalMarginal k p := by
  apply (isKLocalMarginal_iff_maxEntropy_sameFeatureMoments k p).2
  refine ⟨?_, ?_⟩
  · intro scope _
    rfl
  · intro q hMoments
    exact shannonEntropy_le_of_sameFeatureMoments_faceGibbs hFaceGibbs hMoments

/-- Partition function over the positive support of a law. -/
noncomputable def featurePartition
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (p : Distribution (Assignment Var))
    (theta : FeaturePolynomial Var k) : ℝ :=
  ∑ x ∈ UniversalExistence.supportFinset p, Real.exp (theta.eval x)

theorem featurePartition_eq_one_of_logDensity
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (p : Distribution (Assignment Var))
    (theta : FeaturePolynomial Var k)
    (hLog : ∀ x ∈ p.support, Real.log (p x).toReal = theta.eval x) :
    featurePartition p theta = 1 := by
  classical
  let support := UniversalExistence.supportFinset p
  have hpSupport : p.support ⊆ (support : Set (Assignment Var)) := by
    intro x hx
    exact (UniversalExistence.mem_supportFinset p x).2 hx
  rw [featurePartition]
  calc
    ∑ x ∈ support, Real.exp (theta.eval x) =
        ∑ x ∈ support, (p x).toReal := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxSupport : x ∈ p.support :=
            (UniversalExistence.mem_supportFinset p x).1 hx
          rw [← hLog x hxSupport, Real.exp_log]
          exact ENNReal.toReal_pos ((PMF.mem_support_iff p x).1 hxSupport)
            (p.apply_ne_top x)
    _ = 1 := sum_toReal_eq_one_of_support_subset p support hpSupport

/-- The log-density form gives the paper's displayed normalized Gibbs law. -/
theorem normalized_gibbs_formula_of_logDensity
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (p : Distribution (Assignment Var))
    (theta : FeaturePolynomial Var k)
    (hLog : ∀ x ∈ p.support, Real.log (p x).toReal = theta.eval x) :
    ∀ x ∈ p.support,
      (p x).toReal = Real.exp (theta.eval x) / featurePartition p theta := by
  intro x hx
  rw [featurePartition_eq_one_of_logDensity p theta hLog, div_one, ← hLog x hx,
    Real.exp_log]
  exact ENNReal.toReal_pos ((PMF.mem_support_iff p x).1 hx) (p.apply_ne_top x)

end KLocality
