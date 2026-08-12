import KLocality.SelectorTrade
import KLocality.CoordinateSubstitution

namespace KLocality

universe u

/-!
# Ground-state extension complexity

This module turns the type-generic ground-state extension relation into the
paper's latent-bit complexity `GSE_k`, including padding by unused latent bits.
It then states selector facial-closure duality with the manuscript's literal
inequalities `GSE_k(S) ≤ ℓ` and `GSE_k(S) > ℓ`.
-/

/-- Read an old joint assignment from a larger latent cube, ignoring the new
latent coordinates. -/
def latentPaddingRecipe
    (ObsVar : Type u) {smaller larger : Nat} (hSize : smaller ≤ larger) :
    Sum ObsVar (Fin smaller) → CoordinateRecipe (Sum ObsVar (Fin larger))
  | Sum.inl observed => Sum.inl (Sum.inl observed)
  | Sum.inr latent => Sum.inl (Sum.inr (Fin.castLE hSize latent))

@[simp]
theorem substituteAssignment_latentPaddingRecipe_observed
    (ObsVar : Type u) {smaller larger : Nat} (hSize : smaller ≤ larger)
    (assignment : Assignment (Sum ObsVar (Fin larger))) (observed : ObsVar) :
    substituteAssignment (latentPaddingRecipe ObsVar hSize) assignment
        (Sum.inl observed) = assignment (Sum.inl observed) :=
  rfl

@[simp]
theorem substituteAssignment_latentPaddingRecipe_latent
    (ObsVar : Type u) {smaller larger : Nat} (hSize : smaller ≤ larger)
    (assignment : Assignment (Sum ObsVar (Fin larger))) (latent : Fin smaller) :
    substituteAssignment (latentPaddingRecipe ObsVar hSize) assignment
        (Sum.inr latent) = assignment (Sum.inr (Fin.castLE hSize latent)) :=
  rfl

@[simp]
theorem projectObs_substituteAssignment_latentPaddingRecipe
    (ObsVar : Type u) {smaller larger : Nat} (hSize : smaller ≤ larger)
    (assignment : Assignment (Sum ObsVar (Fin larger))) :
    projectObs
        (substituteAssignment (latentPaddingRecipe ObsVar hSize) assignment) =
      projectObs assignment :=
  rfl

/-- Extend an old joint assignment to a larger latent cube, filling every new
coordinate with `false`. -/
def padJointAssignment
    {ObsVar : Type u} {smaller larger : Nat}
    (assignment : Assignment (Sum ObsVar (Fin smaller))) :
    Assignment (Sum ObsVar (Fin larger))
  | Sum.inl observed => assignment (Sum.inl observed)
  | Sum.inr latent =>
      if hLatent : latent.val < smaller then
        assignment (Sum.inr ⟨latent.val, hLatent⟩)
      else false

@[simp]
theorem projectObs_padJointAssignment
    {ObsVar : Type u} {smaller larger : Nat}
    (assignment : Assignment (Sum ObsVar (Fin smaller))) :
    projectObs (padJointAssignment (larger := larger) assignment) =
      projectObs assignment :=
  rfl

@[simp]
theorem substituteAssignment_latentPaddingRecipe_padJointAssignment
    (ObsVar : Type u) {smaller larger : Nat} (hSize : smaller ≤ larger)
    (assignment : Assignment (Sum ObsVar (Fin smaller))) :
    substituteAssignment (latentPaddingRecipe ObsVar hSize)
        (padJointAssignment (larger := larger) assignment) = assignment := by
  funext coordinate
  cases coordinate with
  | inl observed => rfl
  | inr latent =>
      simp only [substituteAssignment_latentPaddingRecipe_latent,
        padJointAssignment, Fin.val_castLE, dif_pos latent.isLt]

/-- Add unused latent bits to a ground-state extension. -/
noncomputable def GroundStateExtension.padLatent
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {k smaller larger : Nat} {visibleSupport : Set (Assignment ObsVar)}
    (extension : GroundStateExtension k ObsVar (Fin smaller) visibleSupport)
    (hSize : smaller ≤ larger) :
    GroundStateExtension k ObsVar (Fin larger) visibleSupport := by
  classical
  let energy := extension.facial.choose
  have hEnergy := extension.facial.choose_spec
  have hNonnegative := hEnergy.1
  have hZeroSet := hEnergy.2
  let recipe := latentPaddingRecipe ObsVar hSize
  let paddedGroundStates : Set (Assignment (Sum ObsVar (Fin larger))) :=
    {assignment |
      substituteAssignment recipe assignment ∈ extension.groundStates}
  let paddedEnergy := energy.substitute recipe
  refine {
    groundStates := paddedGroundStates
    facial := ⟨paddedEnergy, ?_, ?_⟩
    projection := ?_ }
  · intro assignment
    rw [show paddedEnergy.eval assignment =
        energy.eval (substituteAssignment recipe assignment) by
      exact FeaturePolynomial.eval_substitute recipe energy assignment]
    exact hNonnegative _
  · intro assignment
    rw [show paddedEnergy.eval assignment =
        energy.eval (substituteAssignment recipe assignment) by
      exact FeaturePolynomial.eval_substitute recipe energy assignment]
    exact hZeroSet _
  · apply Set.Subset.antisymm
    · rintro visible ⟨assignment, hAssignment, rfl⟩
      have hOldProjection :
          projectObs (substituteAssignment recipe assignment) ∈
            projectObs '' extension.groundStates :=
        ⟨substituteAssignment recipe assignment, hAssignment, rfl⟩
      rw [extension.projection] at hOldProjection
      simpa [recipe] using hOldProjection
    · intro visible hVisible
      have hOldProjection : visible ∈ projectObs '' extension.groundStates := by
        rw [extension.projection]
        exact hVisible
      rcases hOldProjection with ⟨assignment, hAssignment, hProjection⟩
      let padded := padJointAssignment (larger := larger) assignment
      refine ⟨padded, ?_, ?_⟩
      · change substituteAssignment recipe padded ∈ extension.groundStates
        simpa [recipe, padded] using hAssignment
      · simpa [padded] using hProjection

theorem hasGroundStateExtension_padLatent
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {k smaller larger : Nat} {visibleSupport : Set (Assignment ObsVar)}
    (hSize : smaller ≤ larger) :
    HasGroundStateExtension k ObsVar (Fin smaller) visibleSupport →
      HasGroundStateExtension k ObsVar (Fin larger) visibleSupport := by
  rintro ⟨extension⟩
  exact ⟨extension.padLatent hSize⟩

/-- Bit-count specialization of ground-state extension existence. -/
abbrev HasGroundStateExtensionBits
    (k latentBits n : Nat) (visibleSupport : Set (BitVec n)) : Prop :=
  HasGroundStateExtension k (Fin n) (Fin latentBits) visibleSupport

/-- `GSE_k(S)`: the least number of latent bits in a degree-`k`
ground-state extension.  As with `localizationComplexity`, the fallback zero
branch makes the definition total; it is unreachable for nonempty supports
when `k ≥ 2`. -/
noncomputable def groundStateExtensionComplexity
    (k n : Nat) (visibleSupport : Finset (BitVec n)) : Nat := by
  classical
  exact if hExists : ∃ latentBits,
      HasGroundStateExtensionBits k latentBits n
        (visibleSupport : Set (BitVec n)) then
    Nat.find hExists
  else 0

/-- Paper-style notation alias for `GSE_k(S)`. -/
noncomputable abbrev GSE_k
    (k n : Nat) (visibleSupport : Finset (BitVec n)) : Nat :=
  groundStateExtensionComplexity k n visibleSupport

theorem groundStateExtensionComplexity_spec
    (k n : Nat) (visibleSupport : Finset (BitVec n))
    (hExists : ∃ latentBits,
      HasGroundStateExtensionBits k latentBits n
        (visibleSupport : Set (BitVec n))) :
    HasGroundStateExtensionBits k
      (groundStateExtensionComplexity k n visibleSupport) n
      (visibleSupport : Set (BitVec n)) := by
  classical
  simp only [groundStateExtensionComplexity, dif_pos hExists]
  exact Nat.find_spec hExists

theorem groundStateExtensionComplexity_min
    (k n : Nat) (visibleSupport : Finset (BitVec n))
    (latentBits : Nat)
    (hExtension : HasGroundStateExtensionBits k latentBits n
      (visibleSupport : Set (BitVec n))) :
    groundStateExtensionComplexity k n visibleSupport ≤ latentBits := by
  classical
  let hExists : ∃ latentBits,
      HasGroundStateExtensionBits k latentBits n
        (visibleSupport : Set (BitVec n)) := ⟨latentBits, hExtension⟩
  simp only [groundStateExtensionComplexity, dif_pos hExists]
  exact Nat.find_min' hExists hExtension

/-- A localization whose observed support is `visibleSupport` induces the
corresponding ground-state extension. -/
theorem hasGroundStateExtension_of_localization
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {LatVar : Type*} [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {p : Distribution (Assignment ObsVar)}
    {visibleSupport : Set (Assignment ObsVar)}
    (localization : KLocalization k ObsVar LatVar p)
    (hSupport : p.support = visibleSupport) :
    HasGroundStateExtension k ObsVar LatVar visibleSupport := by
  let extension := localization.toGroundStateExtension
  exact ⟨{
    groundStates := extension.groundStates
    facial := extension.facial
    projection := extension.projection.trans hSupport }⟩

/-- Nonempty finite supports always have a ground-state extension in the
paper's range `k ≥ 2`. -/
theorem groundStateExtension_exists
    {k n : Nat} (hk : 2 ≤ k)
    (visibleSupport : Finset (BitVec n))
    (hVisible : visibleSupport.Nonempty) :
    ∃ latentBits, HasGroundStateExtensionBits k latentBits n
      (visibleSupport : Set (BitVec n)) := by
  let p : Distribution (BitVec n) := uniformOn visibleSupport hVisible
  rcases hasKLocalization_supportCard p hk with ⟨localization⟩
  refine ⟨(UniversalExistence.supportFinset p).card, ?_⟩
  exact hasGroundStateExtension_of_localization localization (by
    simp [p])

/-- **Theorem `thm:selector-closure`, complexity form.** -/
theorem groundStateExtensionComplexity_le_iff_exists_selector_doesNotLeak
    {k n latentBits : Nat} (hk : 2 ≤ k)
    (visibleSupport : Finset (BitVec n))
    (hVisible : visibleSupport.Nonempty) :
    groundStateExtensionComplexity k n visibleSupport ≤ latentBits ↔
      ∃ selector : Selector visibleSupport (Fin latentBits),
        SelectorDoesNotLeak k hVisible selector := by
  have hExists := groundStateExtension_exists hk visibleSupport hVisible
  constructor
  · intro hCost
    have hOptimal := groundStateExtensionComplexity_spec
      k n visibleSupport hExists
    have hPadded := hasGroundStateExtension_padLatent hCost hOptimal
    exact (hasGroundStateExtension_iff_exists_selector_doesNotLeak
      k visibleSupport hVisible).1 hPadded
  · rintro ⟨selector, hSafe⟩
    have hExtension : HasGroundStateExtensionBits k latentBits n
        (visibleSupport : Set (BitVec n)) :=
      (hasGroundStateExtension_iff_exists_selector_doesNotLeak
        k visibleSupport hVisible).2 ⟨selector, hSafe⟩
    exact groundStateExtensionComplexity_min
      k n visibleSupport latentBits hExtension

/-- **Theorem `thm:selector-closure`, lower-bound form.** The universal
selector quantifier is now exactly the strict `GSE_k` lower bound. -/
theorem groundStateExtensionComplexity_gt_iff_every_selector_leaks
    {k n latentBits : Nat} (hk : 2 ≤ k)
    (visibleSupport : Finset (BitVec n))
    (hVisible : visibleSupport.Nonempty) :
    latentBits < groundStateExtensionComplexity k n visibleSupport ↔
      ∀ selector : Selector visibleSupport (Fin latentBits),
        SelectorLeaks k hVisible selector := by
  constructor
  · intro hLower selector
    apply (selectorLeaks_iff_not_doesNotLeak k hVisible selector).2
    intro hSafe
    have hUpper :=
      (groundStateExtensionComplexity_le_iff_exists_selector_doesNotLeak
        hk visibleSupport hVisible).2 ⟨selector, hSafe⟩
    exact (Nat.not_le_of_lt hLower) hUpper
  · intro hLeaks
    apply Nat.lt_of_not_ge
    intro hUpper
    rcases
        (groundStateExtensionComplexity_le_iff_exists_selector_doesNotLeak
          hk visibleSupport hVisible).1 hUpper with
      ⟨selector, hSafe⟩
    exact (selectorLeaks_iff_not_doesNotLeak k hVisible selector).1
      (hLeaks selector) hSafe

/-- First inequality in Proposition `prop:facial-cover`: localization
complexity dominates ground-state extension complexity. -/
theorem groundStateExtensionComplexity_le_localizationComplexity
    {k n : Nat} (hk : 2 ≤ k)
    (p : Distribution (BitVec n))
    (visibleSupport : Finset (BitVec n))
    (hSupport : p.support = (visibleSupport : Set (BitVec n))) :
    groundStateExtensionComplexity k n visibleSupport ≤
      localizationComplexityBits k n p := by
  have hLocalization := localizationComplexityBits_spec k n p
    (kLocalization_exists p hk)
  rcases hLocalization with ⟨localization⟩
  exact groundStateExtensionComplexity_min k n visibleSupport
    (localizationComplexityBits k n p)
    (hasGroundStateExtension_of_localization localization hSupport)

end KLocality
