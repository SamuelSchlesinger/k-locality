import KLocality.FeaturePolynomial
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace KLocality

open scoped BigOperators

universe u

/-!
# The finite marginal polytope

This module identifies the polynomial certificate used by `IsFacialSupport`
with the manuscript's literal face of the order-`k` marginal polytope.  Mathlib
calls a face presented by a maximizing functional an `IsExposed` set; every
face of the finite polytope used here has this form.
-/

/-- Ambient vector space of canonical features of order at most `k`. -/
abbrev FeatureVector
    (Var : Type u) [DecidableEq Var] (k : Nat) :=
  FeatureScope Var k → ℝ

/-- The order-`k` marginal polytope, as the convex hull of all Boolean feature
vectors. -/
def marginalPolytope
    {Var : Type u} [Fintype Var] [DecidableEq Var] (k : Nat) :
    Set (FeatureVector Var k) :=
  convexHull ℝ (Set.range (canonicalFeature k))

theorem canonicalFeature_mem_marginalPolytope
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (x : Assignment Var) :
    canonicalFeature k x ∈ marginalPolytope k := by
  apply subset_convexHull ℝ
  exact ⟨x, rfl⟩

namespace FeaturePolynomial

/-- A feature polynomial as a linear functional on feature-vector space. -/
noncomputable def linearFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) :
    FeatureVector Var k →ₗ[ℝ] ℝ where
  toFun vector := ∑ scope, polynomial scope * vector scope
  map_add' left right := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar vector := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro scope _
    ring

@[simp]
theorem linearFunctional_apply
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) (vector : FeatureVector Var k) :
    polynomial.linearFunctional vector =
      ∑ scope, polynomial scope * vector scope :=
  rfl

@[simp]
theorem linearFunctional_canonicalFeature
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) (x : Assignment Var) :
    polynomial.linearFunctional (canonicalFeature k x) = polynomial.eval x :=
  rfl

/-- The continuous functional exposing a feature-polytope face.  Continuity is
automatic because the feature-vector space is finite dimensional. -/
noncomputable def continuousLinearFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) :
    StrongDual ℝ (FeatureVector Var k) :=
  LinearMap.toContinuousLinearMap polynomial.linearFunctional

@[simp]
theorem continuousLinearFunctional_apply
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) (vector : FeatureVector Var k) :
    polynomial.continuousLinearFunctional vector =
      polynomial.linearFunctional vector :=
  rfl

/-- Coordinates of an arbitrary linear functional in the monomial-feature
basis. -/
noncomputable def ofLinearFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (functional : FeatureVector Var k →ₗ[ℝ] ℝ) :
    FeaturePolynomial Var k :=
  fun scope => functional (Pi.single scope 1)

theorem eval_ofLinearFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (functional : FeatureVector Var k →ₗ[ℝ] ℝ)
    (x : Assignment Var) :
    eval (ofLinearFunctional functional) x =
      functional (canonicalFeature k x) := by
  classical
  rw [← Finset.univ_sum_single (canonicalFeature k x), map_sum]
  simp only [eval, ofLinearFunctional, canonicalFeature]
  apply Finset.sum_congr rfl
  intro scope _
  let value : ℝ := monomialValue scope.1 x
  have hSingle :
      (Pi.single scope value : FeatureVector Var k) =
        value • (Pi.single scope (1 : ℝ) : FeatureVector Var k) := by
    ext coordinate
    by_cases hCoordinate : coordinate = scope
    · subst coordinate
      simp [value]
    · simp [hCoordinate]
  calc
    functional (Pi.single scope 1) * value =
        value * functional (Pi.single scope 1) := mul_comm _ _
    _ = functional (value • (Pi.single scope (1 : ℝ) : FeatureVector Var k)) := by
      rw [map_smul, smul_eq_mul]
    _ = functional (Pi.single scope value) := by rw [← hSingle]

/-- The degree-zero feature polynomial with prescribed constant value. -/
noncomputable def constant
    {Var : Type u} [Fintype Var] [DecidableEq Var] (k : Nat) (value : ℝ) :
    FeaturePolynomial Var k :=
  fun scope => if scope = emptyScope Var k then value else 0

@[simp]
theorem eval_constant
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (value : ℝ) (x : Assignment Var) :
    eval (constant k value) x = value := by
  classical
  unfold eval constant
  rw [Fintype.sum_eq_single (emptyScope Var k)]
  · simp only [if_pos]
    change value * monomialValue (∅ : Finset Var) x = value
    rw [monomialValue_empty]
    ring
  · intro scope hNe
    simp [hNe]

@[simp]
theorem eval_add
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (left right : FeaturePolynomial Var k) (x : Assignment Var) :
    eval (left + right) x = eval left x + eval right x := by
  simp [eval, add_mul, Finset.sum_add_distrib]

@[simp]
theorem eval_sub
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (left right : FeaturePolynomial Var k) (x : Assignment Var) :
    eval (left - right) x = eval left x - eval right x := by
  simp [eval, sub_mul, Finset.sum_sub_distrib]

end FeaturePolynomial

/-- Every nonempty polynomially facial support is literally the inverse image
of an exposed face of the finite marginal polytope. -/
theorem exists_exposedFace_preimage_of_isFacialSupport
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {target : Set (Assignment Var)}
    (hTarget : target.Nonempty)
    (hFacial : IsFacialSupport k target) :
    ∃ face : Set (FeatureVector Var k),
      IsExposed ℝ (marginalPolytope k) face ∧
        target = canonicalFeature k ⁻¹' face := by
  classical
  rcases hFacial with ⟨energy, hNonneg, hZero⟩
  rcases hTarget with ⟨anchor, hAnchor⟩
  have hAnchorZero : energy.eval anchor = 0 := (hZero anchor).2 hAnchor
  let exposing : StrongDual ℝ (FeatureVector Var k) :=
    -energy.continuousLinearFunctional
  let face : Set (FeatureVector Var k) :=
    exposing.toExposed (marginalPolytope k)
  have hPolyNonneg : ∀ vector ∈ marginalPolytope k,
      0 ≤ energy.linearFunctional vector := by
    intro vector hVector
    apply (convexHull_min (𝕜 := ℝ) ?_ (convex_halfSpace_ge
      (LinearMap.isLinear energy.linearFunctional) 0)) hVector
    rintro _ ⟨x, rfl⟩
    simpa using hNonneg x
  refine ⟨face, ContinuousLinearMap.toExposed.isExposed, ?_⟩
  ext x
  change x ∈ target ↔ canonicalFeature k x ∈ face
  constructor
  · intro hxTarget
    have hxZero : energy.eval x = 0 := (hZero x).2 hxTarget
    refine ⟨canonicalFeature_mem_marginalPolytope k x, ?_⟩
    intro vector hVector
    have hVectorNonneg := hPolyNonneg vector hVector
    change -energy.linearFunctional vector ≤
      -energy.linearFunctional (canonicalFeature k x)
    rw [FeaturePolynomial.linearFunctional_canonicalFeature, hxZero]
    linarith
  · intro hxFace
    have hCompare := hxFace.2 (canonicalFeature k anchor)
      (canonicalFeature_mem_marginalPolytope k anchor)
    have hxLe : energy.eval x ≤ 0 := by
      change -energy.linearFunctional (canonicalFeature k anchor) ≤
        -energy.linearFunctional (canonicalFeature k x) at hCompare
      rw [FeaturePolynomial.linearFunctional_canonicalFeature,
        FeaturePolynomial.linearFunctional_canonicalFeature, hAnchorZero] at hCompare
      linarith
    exact (hZero x).1 (le_antisymm hxLe (hNonneg x))

/-- Conversely, the inverse image of a nonempty exposed marginal-polytope face
is the zero set of a nonnegative degree-`k` feature polynomial. -/
theorem isFacialSupport_of_exists_exposedFace_preimage
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {target : Set (Assignment Var)}
    (hTarget : target.Nonempty)
    (hFace : ∃ face : Set (FeatureVector Var k),
      IsExposed ℝ (marginalPolytope k) face ∧
        target = canonicalFeature k ⁻¹' face) :
    IsFacialSupport k target := by
  classical
  rcases hTarget with ⟨anchor, hAnchor⟩
  rcases hFace with ⟨face, hExposed, hPreimage⟩
  have hAnchorFace : canonicalFeature k anchor ∈ face := by
    rw [hPreimage] at hAnchor
    exact hAnchor
  rcases hExposed ⟨canonicalFeature k anchor, hAnchorFace⟩ with
    ⟨functional, hFaceEq⟩
  let linearPolynomial : FeaturePolynomial Var k :=
    FeaturePolynomial.ofLinearFunctional functional.toLinearMap
  let energy : FeaturePolynomial Var k :=
    FeaturePolynomial.constant k (functional (canonicalFeature k anchor)) -
      linearPolynomial
  have hEnergyEval : ∀ x,
      energy.eval x = functional (canonicalFeature k anchor) -
        functional (canonicalFeature k x) := by
    intro x
    simp [energy, linearPolynomial, FeaturePolynomial.eval_ofLinearFunctional]
  have hAnchorMax : ∀ vector ∈ marginalPolytope k,
      functional vector ≤ functional (canonicalFeature k anchor) := by
    rw [hFaceEq] at hAnchorFace
    exact hAnchorFace.2
  refine ⟨energy, ?_, ?_⟩
  · intro x
    rw [hEnergyEval x]
    exact sub_nonneg.mpr
      (hAnchorMax (canonicalFeature k x) (canonicalFeature_mem_marginalPolytope k x))
  · intro x
    rw [hEnergyEval x]
    constructor
    · intro hZero
      have hEqual : functional (canonicalFeature k x) =
          functional (canonicalFeature k anchor) := by linarith
      rw [hPreimage, Set.mem_preimage, hFaceEq]
      refine ⟨canonicalFeature_mem_marginalPolytope k x, ?_⟩
      intro vector hVector
      rw [hEqual]
      exact hAnchorMax vector hVector
    · intro hxTarget
      have hxFace : canonicalFeature k x ∈ face := by
        rw [← Set.mem_preimage, ← hPreimage]
        exact hxTarget
      rw [hFaceEq] at hxFace
      have hForward := hxFace.2 (canonicalFeature k anchor)
        (canonicalFeature_mem_marginalPolytope k anchor)
      have hBackward := hAnchorMax (canonicalFeature k x)
        (canonicalFeature_mem_marginalPolytope k x)
      linarith

/-- Certificate faciality and literal exposed-face faciality coincide for a
nonempty support. -/
theorem isFacialSupport_iff_exists_exposedFace_preimage
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {target : Set (Assignment Var)}
    (hTarget : target.Nonempty) :
    IsFacialSupport k target ↔
      ∃ face : Set (FeatureVector Var k),
        IsExposed ℝ (marginalPolytope k) face ∧
          target = canonicalFeature k ⁻¹' face := by
  constructor
  · exact exists_exposedFace_preimage_of_isFacialSupport hTarget
  · exact isFacialSupport_of_exists_exposedFace_preimage hTarget

end KLocality
