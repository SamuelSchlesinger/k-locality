import KLocality.FaceGibbs
import KLocality.FiniteSeparation
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace KLocality

open scoped BigOperators

universe u

/-!
# Exposing maximal moment-fiber supports

This file proves the finite strict-complementarity step behind the forward
direction of the face--Gibbs theorem.
-/

/-- A nonnegative finite weight vector can be perturbed a sufficiently small
positive distance in any direction that is nonnegative on its zero
coordinates. -/
theorem exists_positive_perturbation_nonnegative
    {α : Type u} [Fintype α]
    (base direction : α → ℝ)
    (hBase : ∀ i, 0 ≤ base i)
    (hDirection : ∀ i, base i = 0 → 0 ≤ direction i) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ i, 0 ≤ base i + epsilon * direction i := by
  classical
  have hFinite : ∀ s : Finset α, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ i ∈ s, 0 ≤ base i + epsilon * direction i := by
    intro s
    induction s using Finset.induction with
    | empty =>
        exact ⟨1, zero_lt_one, by simp⟩
    | insert current rest hNotMem ih =>
        rcases ih with ⟨epsilon, hEpsilon, hOnS⟩
        by_cases hDir : 0 ≤ direction current
        · refine ⟨epsilon, hEpsilon, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with hEq | hj
          · subst j
            exact add_nonneg (hBase current) (mul_nonneg hEpsilon.le hDir)
          · exact hOnS j hj
        · have hDirNeg : direction current < 0 := lt_of_not_ge hDir
          have hBasePos : 0 < base current := by
            have hBaseNe : base current ≠ 0 := by
              intro hZero
              exact hDir ((hDirection current hZero))
            exact lt_of_le_of_ne (hBase current) (Ne.symm hBaseNe)
          let bound : ℝ := base current / (-direction current)
          have hBoundPos : 0 < bound := div_pos hBasePos (neg_pos.mpr hDirNeg)
          let epsilon' := min epsilon bound
          have hEpsilon' : 0 < epsilon' := lt_min hEpsilon hBoundPos
          refine ⟨epsilon', hEpsilon', ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with hEq | hj
          · have hLeBound : epsilon' ≤ bound := min_le_right _ _
            have hBoundIdentity : bound * direction current = -base current := by
              dsimp only [bound]
              field_simp [ne_of_lt hDirNeg]
            have hMul : bound * direction current ≤ epsilon' * direction current :=
              mul_le_mul_of_nonpos_right hLeBound hDirNeg.le
            rw [hBoundIdentity] at hMul
            subst j
            linarith
          · have hOld := hOnS j hj
            by_cases hDirJ : 0 ≤ direction j
            · exact add_nonneg (hBase j) (mul_nonneg hEpsilon'.le hDirJ)
            · have hEpsilonLe : epsilon' ≤ epsilon := min_le_left _ _
              have hMul : epsilon * direction j ≤ epsilon' * direction j :=
                mul_le_mul_of_nonpos_right hEpsilonLe (le_of_not_ge hDirJ)
              linarith
  rcases hFinite Finset.univ with ⟨epsilon, hEpsilon, hAll⟩
  exact ⟨epsilon, hEpsilon, fun i => hAll i (Finset.mem_univ i)⟩

/-- Build a PMF from a finite nonnegative real table of total mass one. -/
noncomputable def distributionOfRealWeights
    {α : Type u} [Fintype α]
    (weights : α → ℝ)
    (hNonneg : ∀ i, 0 ≤ weights i)
    (hSum : ∑ i, weights i = 1) : Distribution α := by
  classical
  refine PMF.ofFintype (fun i => ENNReal.ofReal (weights i)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hNonneg i), hSum]
  simp

@[simp]
theorem distributionOfRealWeights_apply_toReal
    {α : Type u} [Fintype α]
    (weights : α → ℝ)
    (hNonneg : ∀ i, 0 ≤ weights i)
    (hSum : ∑ i, weights i = 1) (i : α) :
    (distributionOfRealWeights weights hNonneg hSum i).toReal = weights i := by
  simp [distributionOfRealWeights, hNonneg i]

/-- Assignments outside the support of a PMF. -/
abbrev OutsideSupport
    {Var : Type u} (p : Distribution (Assignment Var)) :=
  {x : Assignment Var // x ∉ p.support}

/-- Restrict a real table to coordinates outside `p.support`. -/
def outsideRestriction
    {Var : Type u} (p : Distribution (Assignment Var)) :
    (Assignment Var → ℝ) →ₗ[ℝ] (OutsideSupport p → ℝ) where
  toFun weights := fun x => weights x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem outsideRestriction_apply
    {Var : Type u} (p : Distribution (Assignment Var))
    (weights : Assignment Var → ℝ) (x : OutsideSupport p) :
    outsideRestriction p weights x = weights x.1 :=
  rfl

theorem sum_direction_eq_zero_of_mem_momentMap_ker
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {direction : Assignment Var → ℝ}
    (hKernel : direction ∈ LinearMap.ker (FeaturePolynomial.momentMap k)) :
    ∑ x, direction x = 0 := by
  have hEmpty := congrFun hKernel (FeaturePolynomial.emptyScope Var k)
  simpa [FeaturePolynomial.momentMap_apply, FeaturePolynomial.emptyScope,
    monomialValue] using hEmpty

/-- A nonnegative outside direction in the moment-map kernel produces a PMF
in the same moment fiber whose outside real weights are positive wherever the
direction is positive. -/
theorem exists_sameMoments_distribution_of_kernel_direction
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (p : Distribution (Assignment Var))
    (direction : Assignment Var → ℝ)
    (hKernel : direction ∈ LinearMap.ker (FeaturePolynomial.momentMap k))
    (hOutside : ∀ x : OutsideSupport p, 0 ≤ direction x.1) :
    ∃ epsilon : ℝ, ∃ q : Distribution (Assignment Var),
      0 < epsilon ∧ SameFeatureMomentsUpTo k p q ∧
        ∀ x : OutsideSupport p, (q x.1).toReal = epsilon * direction x.1 := by
  classical
  let base := FeaturePolynomial.realWeights p
  have hBase : ∀ x, 0 ≤ base x := fun _ => ENNReal.toReal_nonneg
  have hDirectionAtZero : ∀ x, base x = 0 → 0 ≤ direction x := by
    intro x hx
    have hpZero : p x = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (p x)).1 hx with hpZero | hpTop
      · exact hpZero
      · exact False.elim ((p.apply_ne_top x) hpTop)
    exact hOutside ⟨x, (p.apply_eq_zero_iff x).1 hpZero⟩
  rcases exists_positive_perturbation_nonnegative base direction hBase hDirectionAtZero with
    ⟨epsilon, hEpsilon, hNonneg⟩
  let weights : Assignment Var → ℝ := fun x => base x + epsilon * direction x
  have hBaseSum : ∑ x, base x = 1 := by
    simpa [base] using sum_toReal_eq_one_of_support_subset p Finset.univ
      (by intro x _; simp)
  have hDirectionSum : ∑ x, direction x = 0 :=
    sum_direction_eq_zero_of_mem_momentMap_ker hKernel
  have hWeightsSum : ∑ x, weights x = 1 := by
    simp only [weights, Finset.sum_add_distrib, ← Finset.mul_sum,
      hBaseSum, hDirectionSum, mul_zero, add_zero]
  let q := distributionOfRealWeights weights hNonneg hWeightsSum
  have hqWeights : ∀ x, (q x).toReal = weights x := by
    intro x
    exact distributionOfRealWeights_apply_toReal weights hNonneg hWeightsSum x
  have hMomentMap : FeaturePolynomial.momentMap k
      (FeaturePolynomial.realWeights q) =
      FeaturePolynomial.momentMap k (FeaturePolynomial.realWeights p) := by
    funext scope
    rw [FeaturePolynomial.momentMap_apply, FeaturePolynomial.momentMap_apply]
    simp_rw [FeaturePolynomial.realWeights, hqWeights]
    simp only [weights, add_mul, Finset.sum_add_distrib]
    have hScopeZero := congrFun hKernel scope
    have hDirectionMoment :
        ∑ x, direction x * monomialValue scope.1 x = 0 := by
      simpa [FeaturePolynomial.momentMap_apply] using hScopeZero
    have hFactor :
        (∑ x, epsilon * direction x * monomialValue scope.1 x) =
          epsilon * ∑ x, direction x * monomialValue scope.1 x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hFactor, hDirectionMoment, mul_zero, add_zero]
    rfl
  refine ⟨epsilon, q, hEpsilon,
    (FeaturePolynomial.sameFeatureMomentsUpTo_iff_momentMap_realWeights_eq k p q).2
      hMomentMap, ?_⟩
  intro x
  rw [hqWeights]
  simp only [weights, base, FeaturePolynomial.realWeights]
  have hpZero : p x.1 = 0 := (p.apply_eq_zero_iff x.1).2 x.2
  simp [hpZero]

/-- Outside-coordinate projection of the moment-map kernel. -/
noncomputable def outsideKernelImage
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    Submodule ℝ (OutsideSupport p → ℝ) :=
  (LinearMap.ker (FeaturePolynomial.momentMap k)).map (outsideRestriction p)

/-- Maximality of `p.support` in its moment fiber says precisely that the
outside projection of the tangent space misses the positive simplex. -/
theorem outsideKernelImage_disjoint_stdSimplex
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    [Fintype (OutsideSupport p)]
    (hMaxSupport : ∀ q : Distribution (Assignment Var),
      SameFeatureMomentsUpTo k p q → q.support ⊆ p.support) :
    Disjoint (outsideKernelImage k p : Set (OutsideSupport p → ℝ))
      (stdSimplex ℝ (OutsideSupport p)) := by
  classical
  apply Set.disjoint_left.mpr
  intro outsideDirection hImage hSimplex
  rcases hImage with ⟨direction, hKernel, hRestriction⟩
  have hOutsideNonneg : ∀ x : OutsideSupport p, 0 ≤ direction x.1 := by
    intro x
    have := hSimplex.1 x
    simpa [← hRestriction] using this
  rcases exists_sameMoments_distribution_of_kernel_direction p direction hKernel
      hOutsideNonneg with ⟨epsilon, q, hEpsilon, hMoments, hOutsideWeights⟩
  have hPositiveCoordinate : ∃ x : OutsideSupport p, 0 < outsideDirection x := by
    by_contra hNone
    push_neg at hNone
    have hZero : ∀ x : OutsideSupport p, outsideDirection x = 0 := by
      intro x
      exact le_antisymm (hNone x) (hSimplex.1 x)
    have hSumZero : ∑ x, outsideDirection x = 0 := by simp [hZero]
    exact zero_ne_one (hSumZero.symm.trans hSimplex.2)
  rcases hPositiveCoordinate with ⟨x, hxPositive⟩
  have hDirectionPositive : 0 < direction x.1 := by
    simpa [← hRestriction] using hxPositive
  have hqPositive : 0 < (q x.1).toReal := by
    rw [hOutsideWeights x]
    exact mul_pos hEpsilon hDirectionPositive
  have hqSupport : x.1 ∈ q.support := by
    apply (PMF.mem_support_iff q x.1).2
    intro hZero
    rw [hZero, ENNReal.toReal_zero] at hqPositive
    exact (lt_irrefl 0) hqPositive
  exact x.2 (hMaxSupport q hMoments hqSupport)

/-- Extend a functional on outside coordinates to all real weight tables. -/
noncomputable def extendOutsideFunctional
    {Var : Type u} (p : Distribution (Assignment Var))
    (functional : (OutsideSupport p → ℝ) →ₗ[ℝ] ℝ) :
    (Assignment Var → ℝ) →ₗ[ℝ] ℝ :=
  functional.comp (outsideRestriction p)

@[simp]
theorem extendOutsideFunctional_apply
    {Var : Type u} (p : Distribution (Assignment Var))
    (functional : (OutsideSupport p → ℝ) →ₗ[ℝ] ℝ)
    (weights : Assignment Var → ℝ) :
    extendOutsideFunctional p functional weights =
      functional (outsideRestriction p weights) :=
  rfl

/-- Every maximal canonical moment-fiber support has a nonnegative
degree-`k` exposing polynomial. -/
theorem isFacialSupport_of_maximal_momentFiber_support
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hMaxSupport : ∀ q : Distribution (Assignment Var),
      SameFeatureMomentsUpTo k p q → q.support ⊆ p.support) :
    IsFacialSupport k p.support := by
  classical
  have hDisjoint := outsideKernelImage_disjoint_stdSimplex k p hMaxSupport
  rcases exists_strictlyPositive_annihilator (outsideKernelImage k p) hDisjoint with
    ⟨outsideFunctional, hVanish, hPositive⟩
  let fullFunctional := extendOutsideFunctional p outsideFunctional
  have hKernelLe :
      ⨅ scope : FeatureScope Var k,
          LinearMap.ker (FeaturePolynomial.momentFunctional scope) ≤
        LinearMap.ker fullFunctional := by
    intro direction hDirection
    have hMomentKernel :
        direction ∈ LinearMap.ker (FeaturePolynomial.momentMap k) := by
      change FeaturePolynomial.momentMap k direction = 0
      funext scope
      exact (Submodule.mem_iInf _).1 hDirection scope
    have hOutsideImage : outsideRestriction p direction ∈ outsideKernelImage k p := by
      exact ⟨direction, hMomentKernel, rfl⟩
    change fullFunctional direction = 0
    exact hVanish (outsideRestriction p direction) hOutsideImage
  have hSpan : fullFunctional ∈ Submodule.span ℝ
      (Set.range (FeaturePolynomial.momentFunctional :
        FeatureScope Var k → (Assignment Var → ℝ) →ₗ[ℝ] ℝ)) :=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker hKernelLe
  rcases (Submodule.mem_span_range_iff_exists_fun ℝ).1 hSpan with
    ⟨energy, hEnergy⟩
  have hEval : ∀ x : Assignment Var,
      FeaturePolynomial.eval energy x = fullFunctional (Pi.single x 1) := by
    intro x
    have hAtX := LinearMap.congr_fun hEnergy (Pi.single x 1)
    simpa [FeaturePolynomial.eval] using hAtX
  refine ⟨energy, ?_, ?_⟩
  · intro x
    rw [hEval x]
    by_cases hx : x ∈ p.support
    · have hRestrictionZero : outsideRestriction p (Pi.single x 1) = 0 := by
        funext y
        simp only [outsideRestriction_apply, Pi.zero_apply]
        rw [Pi.single_eq_of_ne]
        intro hxy
        exact y.2 (hxy ▸ hx)
      simp [fullFunctional, extendOutsideFunctional, hRestrictionZero]
    · let outsideX : OutsideSupport p := ⟨x, hx⟩
      have hRestrictionSingle :
          outsideRestriction p (Pi.single x 1) = Pi.single outsideX 1 := by
        funext y
        simp only [outsideRestriction_apply, Pi.single_apply]
        by_cases hy : y = outsideX
        · simp [hy, outsideX]
        · have hValNe : y.1 ≠ x := by
            intro hVal
            apply hy
            exact Subtype.ext hVal
          simp [hy, hValNe]
      rw [show fullFunctional (Pi.single x 1) =
          outsideFunctional (outsideRestriction p (Pi.single x 1)) by rfl,
        hRestrictionSingle]
      exact (hPositive outsideX).le
  · intro x
    rw [hEval x]
    constructor
    · intro hZero
      by_contra hx
      let outsideX : OutsideSupport p := ⟨x, hx⟩
      have hRestrictionSingle :
          outsideRestriction p (Pi.single x 1) = Pi.single outsideX 1 := by
        funext y
        simp only [outsideRestriction_apply, Pi.single_apply]
        by_cases hy : y = outsideX
        · simp [hy, outsideX]
        · have hValNe : y.1 ≠ x := by
            intro hVal
            apply hy
            exact Subtype.ext hVal
          simp [hy, hValNe]
      have hStrict := hPositive outsideX
      have hStrictFull : 0 < fullFunctional (Pi.single x 1) := by
        rw [show fullFunctional (Pi.single x 1) =
            outsideFunctional (outsideRestriction p (Pi.single x 1)) by rfl,
          hRestrictionSingle]
        exact hStrict
      rw [hZero] at hStrictFull
      exact (lt_irrefl 0) hStrictFull
    · intro hx
      have hRestrictionZero : outsideRestriction p (Pi.single x 1) = 0 := by
        funext y
        simp only [outsideRestriction_apply, Pi.zero_apply]
        rw [Pi.single_eq_of_ne]
        intro hxy
        exact y.2 (hxy ▸ hx)
      simp [fullFunctional, extendOutsideFunctional, hRestrictionZero]

/-- A `k`-local law has facial support. -/
theorem isFacialSupport_of_isKLocalMarginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hLocal : IsKLocalMarginal k p) :
    IsFacialSupport k p.support := by
  apply isFacialSupport_of_maximal_momentFiber_support k p
  intro q hMoments
  exact support_subset_of_sameFeatureMoments_of_isKLocal k hLocal hMoments

end KLocality
