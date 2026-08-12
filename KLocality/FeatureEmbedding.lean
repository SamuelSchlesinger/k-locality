import KLocality.Reindex

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Embedding feature polynomials into larger Boolean cubes

An injection of variable sets sends every monomial scope to a scope of the
same cardinality.  Extending a polynomial along this injection therefore does
not increase its degree.
-/

/-- Map a bounded feature scope along an embedding of variables. -/
def featureScopeEmbedding
    {Var : Type u} {Var' : Type v}
    [DecidableEq Var] [DecidableEq Var']
    (embedding : Var ↪ Var') (k : Nat) :
    FeatureScope Var k ↪ FeatureScope Var' k where
  toFun scope :=
    ⟨scope.1.map embedding, by simpa using scope.2⟩
  inj' := by
    intro left right hEq
    apply Subtype.ext
    exact Finset.map_injective embedding (Subtype.ext_iff.mp hEq)

/-- A single canonical monomial coefficient. -/
noncomputable def FeaturePolynomial.single
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (scope : FeatureScope Var k) (coefficient : ℝ) :
    FeaturePolynomial Var k :=
  fun candidate => if candidate = scope then coefficient else 0

@[simp]
theorem FeaturePolynomial.eval_single
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (scope : FeatureScope Var k) (coefficient : ℝ)
    (x : Assignment Var) :
    (FeaturePolynomial.single scope coefficient).eval x =
      coefficient * monomialValue scope.1 x := by
  classical
  unfold FeaturePolynomial.eval FeaturePolynomial.single
  rw [Fintype.sum_eq_single scope]
  · simp
  · intro candidate hNe
    simp [hNe]

/-- Evaluation commutes with a finite sum of feature polynomials. -/
theorem FeaturePolynomial.eval_finset_sum
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    {ι : Type v} (indices : Finset ι)
    (polynomials : ι → FeaturePolynomial Var k)
    (x : Assignment Var) :
    FeaturePolynomial.eval (∑ i ∈ indices, polynomials i) x =
      ∑ i ∈ indices, FeaturePolynomial.eval (polynomials i) x := by
  classical
  unfold FeaturePolynomial.eval
  simp_rw [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Extend a polynomial along an embedding of its variables. -/
noncomputable def FeaturePolynomial.extendAlong
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    {k : Nat} (embedding : Var ↪ Var')
    (polynomial : FeaturePolynomial Var k) :
    FeaturePolynomial Var' k :=
  ∑ scope : FeatureScope Var k,
    FeaturePolynomial.single (featureScopeEmbedding embedding k scope)
      (polynomial scope)

theorem monomialValue_map_embedding
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    (embedding : Var ↪ Var') (scope : Finset Var)
    (x : Assignment Var') :
    monomialValue (scope.map embedding) x =
      monomialValue scope (fun coordinate => x (embedding coordinate)) := by
  classical
  unfold monomialValue
  have hSubset : scope.map embedding ⊆ trueCoordinates x ↔
      scope ⊆ trueCoordinates (fun coordinate => x (embedding coordinate)) := by
    constructor
    · intro h coordinate hCoordinate
      rw [mem_trueCoordinates]
      have hImage : embedding coordinate ∈ scope.map embedding := by simp [hCoordinate]
      have := h hImage
      simpa only [mem_trueCoordinates] using this
    · intro h coordinate hCoordinate
      rcases Finset.mem_map.mp hCoordinate with ⟨source, hSource, rfl⟩
      rw [mem_trueCoordinates]
      simpa only [mem_trueCoordinates] using h hSource
  by_cases h : scope ⊆ trueCoordinates (fun coordinate => x (embedding coordinate))
  · have hMapped := hSubset.2 h
    simp [h, hMapped]
  · have hMapped : ¬scope.map embedding ⊆ trueCoordinates x := by
      intro hContra
      exact h (hSubset.1 hContra)
    simp [h, hMapped]

@[simp]
theorem FeaturePolynomial.eval_extendAlong
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    {k : Nat} (embedding : Var ↪ Var')
    (polynomial : FeaturePolynomial Var k) (x : Assignment Var') :
    (polynomial.extendAlong embedding).eval x =
      polynomial.eval (fun coordinate => x (embedding coordinate)) := by
  classical
  unfold FeaturePolynomial.extendAlong
  rw [FeaturePolynomial.eval_finset_sum Finset.univ]
  simp only [FeaturePolynomial.eval_single]
  unfold FeaturePolynomial.eval
  apply Finset.sum_congr rfl
  intro scope _
  change polynomial scope * monomialValue (scope.1.map embedding) x = _
  rw [monomialValue_map_embedding]

end KLocality
