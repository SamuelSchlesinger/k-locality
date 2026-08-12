import KLocality.FeatureEmbedding

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Boolean coordinate substitutions

A coordinate of the source cube may be replaced by a target coordinate or by
a Boolean constant.  Reusing a target coordinate models duplication.  Such a
substitution never increases multilinear degree: repeated variables collapse
and fixed coordinates disappear (or kill a monomial when fixed to false).
-/

/-- A coordinate is supplied either by a target variable or a fixed Boolean
constant. -/
abbrev CoordinateRecipe (Target : Type v) := Sum Target Bool

/-- Apply a duplication/fixing recipe to a target assignment. -/
def substituteAssignment
    {Source : Type u} {Target : Type v}
    (recipe : Source → CoordinateRecipe Target)
    (assignment : Assignment Target) : Assignment Source :=
  fun source => match recipe source with
    | Sum.inl target => assignment target
    | Sum.inr value => value

@[simp]
theorem substituteAssignment_apply_variable
    {Source : Type u} {Target : Type v}
    (recipe : Source → CoordinateRecipe Target)
    (assignment : Assignment Target) {source : Source} {target : Target}
    (hRecipe : recipe source = Sum.inl target) :
    substituteAssignment recipe assignment source = assignment target := by
  simp [substituteAssignment, hRecipe]

@[simp]
theorem substituteAssignment_apply_constant
    {Source : Type u} {Target : Type v}
    (recipe : Source → CoordinateRecipe Target)
    (assignment : Assignment Target) {source : Source} {value : Bool}
    (hRecipe : recipe source = Sum.inr value) :
    substituteAssignment recipe assignment source = value := by
  simp [substituteAssignment, hRecipe]

/-- Target variables occurring in the substitution of one source monomial. -/
def substitutedScope
    {Source : Type u} {Target : Type v} [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target)
    (scope : Finset Source) : Finset Target :=
  scope.biUnion fun source => match recipe source with
    | Sum.inl target => {target}
    | Sum.inr _ => ∅

@[simp]
theorem mem_substitutedScope
    {Source : Type u} {Target : Type v} [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target)
    (scope : Finset Source) (target : Target) :
    target ∈ substitutedScope recipe scope ↔
      ∃ source ∈ scope, recipe source = Sum.inl target := by
  classical
  simp only [substitutedScope, Finset.mem_biUnion]
  constructor
  · rintro ⟨source, hSource, hTarget⟩
    cases hRecipe : recipe source with
    | inl value =>
        simp only [hRecipe, Finset.mem_singleton] at hTarget
        subst value
        exact ⟨source, hSource, hRecipe⟩
    | inr value => simp [hRecipe] at hTarget
  · rintro ⟨source, hSource, hRecipe⟩
    exact ⟨source, hSource, by simp [hRecipe]⟩

/-- The substituted scope has no more variables than the original scope. -/
theorem substitutedScope_card_le
    {Source : Type u} {Target : Type v} [DecidableEq Source] [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target)
    (scope : Finset Source) :
    (substitutedScope recipe scope).card ≤ scope.card := by
  classical
  induction scope using Finset.induction with
  | empty => simp [substitutedScope]
  | @insert source rest hNotMem ih =>
      let contribution : Finset Target := match recipe source with
        | Sum.inl target => {target}
        | Sum.inr _ => ∅
      have hContribution : contribution.card ≤ 1 := by
        cases hRecipe : recipe source <;> simp [contribution, hRecipe]
      have hUnion : substitutedScope recipe (insert source rest) =
          contribution ∪ substitutedScope recipe rest := by
        simp [substitutedScope, contribution]
      rw [hUnion]
      calc
        (contribution ∪ substitutedScope recipe rest).card ≤
            contribution.card + (substitutedScope recipe rest).card :=
          Finset.card_union_le _ _
        _ ≤ 1 + rest.card := Nat.add_le_add hContribution ih
        _ = (insert source rest).card := by simp [hNotMem, Nat.add_comm]

/-- A source scope after coordinate substitution, still bounded by `k`. -/
def substitutedFeatureScope
    {Source : Type u} {Target : Type v}
    [DecidableEq Source] [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target) {k : Nat}
    (scope : FeatureScope Source k) : FeatureScope Target k :=
  ⟨substitutedScope recipe scope.1,
    Nat.le_trans (substitutedScope_card_le recipe scope.1) scope.2⟩

/-- A source monomial is killed when one of its coordinates is fixed false. -/
def ScopeHasFalseConstant
    {Source : Type u} {Target : Type v}
    (recipe : Source → CoordinateRecipe Target)
    (scope : Finset Source) : Prop :=
  ∃ source ∈ scope, recipe source = Sum.inr false

/-- A false fixed coordinate kills its source monomial. -/
theorem monomialValue_substituteAssignment_of_false
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target)
    (scope : Finset Source) (assignment : Assignment Target)
    (hFalse : ScopeHasFalseConstant recipe scope) :
    monomialValue scope (substituteAssignment recipe assignment) = 0 := by
  rcases hFalse with ⟨source, hSource, hRecipe⟩
  have hNotSubset : ¬scope ⊆
      trueCoordinates (substituteAssignment recipe assignment) := by
    intro hSubset
    have hTrue := hSubset hSource
    rw [mem_trueCoordinates] at hTrue
    simp [substituteAssignment, hRecipe] at hTrue
  unfold monomialValue
  rw [if_neg hNotSubset]

/-- With no false fixed coordinate, a substituted monomial is exactly the
monomial on the set of target variables which occur in its recipe. -/
theorem monomialValue_substituteAssignment_of_not_false
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target)
    (scope : Finset Source) (assignment : Assignment Target)
    (hFalse : ¬ScopeHasFalseConstant recipe scope) :
    monomialValue scope (substituteAssignment recipe assignment) =
      monomialValue (substitutedScope recipe scope) assignment := by
  classical
  have hSubset :
      substitutedScope recipe scope ⊆ trueCoordinates assignment ↔
        scope ⊆ trueCoordinates (substituteAssignment recipe assignment) := by
    constructor
    · intro hTarget source hSource
      rw [mem_trueCoordinates]
      cases hRecipe : recipe source with
      | inl target =>
          have hTargetMem : target ∈ substitutedScope recipe scope :=
            (mem_substitutedScope recipe scope target).2
              ⟨source, hSource, hRecipe⟩
          have hTrue := hTarget hTargetMem
          rw [mem_trueCoordinates] at hTrue
          simpa [substituteAssignment, hRecipe] using hTrue
      | inr value =>
          cases value with
          | false => exact False.elim (hFalse ⟨source, hSource, hRecipe⟩)
          | true => simp [substituteAssignment, hRecipe]
    · intro hSource target hTarget
      rcases (mem_substitutedScope recipe scope target).1 hTarget with
        ⟨source, hSourceMem, hRecipe⟩
      have hTrue := hSource hSourceMem
      rw [mem_trueCoordinates] at hTrue ⊢
      simpa [substituteAssignment, hRecipe] using hTrue
  unfold monomialValue
  by_cases hTarget : substitutedScope recipe scope ⊆ trueCoordinates assignment
  · have hSource := hSubset.1 hTarget
    rw [if_pos hSource, if_pos hTarget]
  · have hSource : ¬scope ⊆
        trueCoordinates (substituteAssignment recipe assignment) := by
      intro hContra
      exact hTarget (hSubset.2 hContra)
    rw [if_neg hSource, if_neg hTarget]

/-- Substitute one source monomial. -/
noncomputable def FeaturePolynomial.substituteMonomial
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target) {k : Nat}
    (polynomial : FeaturePolynomial Source k)
    (scope : FeatureScope Source k) : FeaturePolynomial Target k := by
  classical
  exact if ScopeHasFalseConstant recipe scope.1 then 0
    else FeaturePolynomial.single (substitutedFeatureScope recipe scope)
      (polynomial scope)

/-- Substitute variables, duplicates, and constants throughout a canonical
feature polynomial. -/
noncomputable def FeaturePolynomial.substitute
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target) {k : Nat}
    (polynomial : FeaturePolynomial Source k) : FeaturePolynomial Target k :=
  ∑ scope : FeatureScope Source k,
    polynomial.substituteMonomial recipe scope

@[simp]
theorem FeaturePolynomial.eval_substitute
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (recipe : Source → CoordinateRecipe Target) {k : Nat}
    (polynomial : FeaturePolynomial Source k)
    (assignment : Assignment Target) :
    (polynomial.substitute recipe).eval assignment =
      polynomial.eval (substituteAssignment recipe assignment) := by
  classical
  unfold FeaturePolynomial.substitute
  calc
    FeaturePolynomial.eval
        (∑ scope : FeatureScope Source k,
          polynomial.substituteMonomial recipe scope) assignment =
        ∑ scope : FeatureScope Source k,
          (polynomial.substituteMonomial recipe scope).eval assignment := by
      rw [FeaturePolynomial.eval_finset_sum Finset.univ]
    _ = ∑ scope : FeatureScope Source k,
        polynomial scope *
          monomialValue scope.1 (substituteAssignment recipe assignment) := by
      apply Finset.sum_congr rfl
      intro scope _
      by_cases hFalse : ScopeHasFalseConstant recipe scope.1
      · rw [monomialValue_substituteAssignment_of_false recipe scope.1 assignment hFalse]
        simp [FeaturePolynomial.substituteMonomial, hFalse,
          FeaturePolynomial.eval]
      · rw [monomialValue_substituteAssignment_of_not_false
          recipe scope.1 assignment hFalse]
        simp [FeaturePolynomial.substituteMonomial, hFalse,
          FeaturePolynomial.eval_single, substitutedFeatureScope]
    _ = polynomial.eval (substituteAssignment recipe assignment) := rfl

end KLocality
