import KLocality.GroundStateExtension

namespace KLocality

open scoped BigOperators

universe u

/-!
# Padding localizations with unused latent bits

A localization using `smaller` latent bits can be regarded as one using any
larger number: embed its joint law by fixing all newly added latent bits to
`false`.  Unary penalties expose those fixed coordinates, so this operation
preserves every locality order at least one.
-/

/-- The fixed-false embedding is injective when the target latent cube is at
least as large as the source. -/
theorem padJointAssignment_injective
    {ObsVar : Type u} {smaller larger : Nat} (hSize : smaller ≤ larger) :
    Function.Injective
      (padJointAssignment (ObsVar := ObsVar) (smaller := smaller)
        (larger := larger)) := by
  intro left right hPadded
  have hRestricted := congrArg
    (substituteAssignment (latentPaddingRecipe ObsVar hSize)) hPadded
  simpa using hRestricted

/-- A joint PMF embedded into a larger latent cube with all new bits fixed
to `false`. -/
noncomputable def padLatentDistribution
    {ObsVar : Type u} {smaller larger : Nat}
    (joint : Distribution (Assignment (Sum ObsVar (Fin smaller)))) :
    Distribution (Assignment (Sum ObsVar (Fin larger))) :=
  joint.map (padJointAssignment (larger := larger))

/-- Padding does not change the mass of an embedded joint assignment. -/
@[simp]
theorem padLatentDistribution_apply_padJointAssignment
    {ObsVar : Type u} {smaller larger : Nat} (hSize : smaller ≤ larger)
    (joint : Distribution (Assignment (Sum ObsVar (Fin smaller))))
    (assignment : Assignment (Sum ObsVar (Fin smaller))) :
    padLatentDistribution (larger := larger) joint
        (padJointAssignment (larger := larger) assignment) =
      joint assignment := by
  rw [padLatentDistribution, PMF.map_apply]
  rw [tsum_eq_single assignment]
  · simp
  · intro other hOther
    have hPaddedNe :
        padJointAssignment (larger := larger) assignment ≠
          padJointAssignment (larger := larger) other := by
      intro hEqual
      exact hOther ((padJointAssignment_injective hSize hEqual).symm)
    simp [hPaddedNe]

/-- The support of the padded law is the image of the old support. -/
theorem support_padLatentDistribution
    {ObsVar : Type u} {smaller larger : Nat}
    (joint : Distribution (Assignment (Sum ObsVar (Fin smaller)))) :
    (padLatentDistribution (larger := larger) joint).support =
      padJointAssignment (larger := larger) '' joint.support := by
  rw [padLatentDistribution, PMF.support_map]

/-- Every newly added latent coordinate is fixed to `false`. -/
def NewLatentsFalse
    {ObsVar : Type u} (smaller : Nat) {larger : Nat}
    (assignment : Assignment (Sum ObsVar (Fin larger))) : Prop :=
  ∀ latent : Fin larger, smaller ≤ latent.val →
    assignment (Sum.inr latent) = false

theorem newLatentsFalse_padJointAssignment
    {ObsVar : Type u} {smaller larger : Nat}
    (assignment : Assignment (Sum ObsVar (Fin smaller))) :
    NewLatentsFalse smaller
      (padJointAssignment (larger := larger) assignment) := by
  intro latent hNew
  simp only [padJointAssignment]
  rw [dif_neg (by omega)]

/-- Restricting to the old coordinates and padding back reconstructs any
assignment whose new coordinates are all false. -/
theorem padJointAssignment_substituteAssignment
    {ObsVar : Type u} {smaller larger : Nat} (hSize : smaller ≤ larger)
    (assignment : Assignment (Sum ObsVar (Fin larger)))
    (hNew : NewLatentsFalse smaller assignment) :
    padJointAssignment (larger := larger)
        (substituteAssignment (latentPaddingRecipe ObsVar hSize) assignment) =
      assignment := by
  funext coordinate
  cases coordinate with
  | inl observed => rfl
  | inr latent =>
      simp only [padJointAssignment]
      split
      next hOld =>
        change assignment
            (Sum.inr (Fin.castLE hSize ⟨latent.val, hOld⟩)) =
          assignment (Sum.inr latent)
        congr 2
      next hNotOld =>
        exact (hNew latent (by omega)).symm

/-- Unary order-`k` energy penalizing every newly added true latent bit. -/
noncomputable def latentPaddingEnergy
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (k smaller larger : Nat) (hk : 1 ≤ k) :
    FeaturePolynomial (Sum ObsVar (Fin larger)) k :=
  ∑ latent : Fin larger,
    if smaller ≤ latent.val then
      FeaturePolynomial.single
        (⟨{Sum.inr latent}, by simpa using hk⟩ :
          FeatureScope (Sum ObsVar (Fin larger)) k) 1
    else 0

@[simp]
theorem monomialValue_singleton_eq_indicator
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (coordinate : Var) (assignment : Assignment Var) :
    monomialValue {coordinate} assignment =
      if assignment coordinate then 1 else 0 := by
  cases hValue : assignment coordinate <;> simp [monomialValue, hValue]

theorem latentPaddingEnergy_eval
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (k smaller larger : Nat) (hk : 1 ≤ k)
    (assignment : Assignment (Sum ObsVar (Fin larger))) :
    (latentPaddingEnergy (ObsVar := ObsVar) k smaller larger hk).eval assignment =
      ∑ latent : Fin larger,
        if smaller ≤ latent.val then
          if assignment (Sum.inr latent) then 1 else 0
        else 0 := by
  classical
  unfold latentPaddingEnergy
  rw [FeaturePolynomial.eval_finset_sum Finset.univ]
  apply Finset.sum_congr rfl
  intro latent _
  by_cases hNew : smaller ≤ latent.val
  · simp [hNew, FeaturePolynomial.eval_single,
      monomialValue_singleton_eq_indicator]
  · simp [hNew, FeaturePolynomial.eval]

theorem latentPaddingEnergy_nonnegative
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (k smaller larger : Nat) (hk : 1 ≤ k)
    (assignment : Assignment (Sum ObsVar (Fin larger))) :
    0 ≤ (latentPaddingEnergy (ObsVar := ObsVar)
      k smaller larger hk).eval assignment := by
  rw [latentPaddingEnergy_eval (ObsVar := ObsVar) k smaller larger hk assignment]
  positivity

theorem latentPaddingEnergy_eq_zero_iff
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (k smaller larger : Nat) (hk : 1 ≤ k)
    (assignment : Assignment (Sum ObsVar (Fin larger))) :
    (latentPaddingEnergy (ObsVar := ObsVar)
        k smaller larger hk).eval assignment = 0 ↔
      NewLatentsFalse smaller assignment := by
  rw [latentPaddingEnergy_eval (ObsVar := ObsVar) k smaller larger hk assignment]
  constructor
  · intro hSum latent hNew
    have hTermNonnegative : ∀ candidate ∈
        (Finset.univ : Finset (Fin larger)),
        0 ≤ (if smaller ≤ candidate.val then
          if assignment (Sum.inr candidate) then (1 : ℝ) else 0
        else 0) := by
      intro candidate _
      by_cases hCandidate : smaller ≤ candidate.val <;>
        cases assignment (Sum.inr candidate) <;> simp [hCandidate]
    have hTermLe := Finset.single_le_sum hTermNonnegative
      (Finset.mem_univ latent)
    rw [hSum] at hTermLe
    cases hValue : assignment (Sum.inr latent)
    · rfl
    · simp [hNew, hValue] at hTermLe
      norm_num at hTermLe
  · intro hNew
    apply Finset.sum_eq_zero
    intro latent _
    by_cases hLatent : smaller ≤ latent.val
    · simp [hLatent, hNew latent hLatent]
    · simp [hLatent]

/-- Fixed-false padding preserves a face--Gibbs certificate. -/
theorem isFaceGibbs_padLatentDistribution
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {smaller larger k : Nat} (hk : 1 ≤ k) (hSize : smaller ≤ larger)
    (joint : Distribution (Assignment (Sum ObsVar (Fin smaller))))
    (hFaceGibbs : IsFaceGibbs k joint) :
    IsFaceGibbs k (padLatentDistribution (larger := larger) joint) := by
  classical
  rcases hFaceGibbs with ⟨⟨energy, hEnergyNonnegative, hEnergyZero⟩,
    theta, hLogDensity⟩
  let recipe := latentPaddingRecipe ObsVar hSize
  let paddedEnergy := energy.substitute recipe +
    latentPaddingEnergy (ObsVar := ObsVar) k smaller larger hk
  let paddedTheta := theta.substitute recipe
  refine ⟨⟨paddedEnergy, ?_, ?_⟩, paddedTheta, ?_⟩
  · intro assignment
    rw [show paddedEnergy.eval assignment =
        energy.eval (substituteAssignment recipe assignment) +
          (latentPaddingEnergy (ObsVar := ObsVar)
            k smaller larger hk).eval assignment by
      simp [paddedEnergy, recipe]]
    exact add_nonneg (hEnergyNonnegative _)
      (latentPaddingEnergy_nonnegative k smaller larger hk assignment)
  · intro assignment
    rw [show paddedEnergy.eval assignment =
        energy.eval (substituteAssignment recipe assignment) +
          (latentPaddingEnergy (ObsVar := ObsVar)
            k smaller larger hk).eval assignment by
      simp [paddedEnergy, recipe]]
    rw [add_eq_zero_iff_of_nonneg (hEnergyNonnegative _)
      (latentPaddingEnergy_nonnegative k smaller larger hk assignment)]
    rw [hEnergyZero, latentPaddingEnergy_eq_zero_iff]
    rw [support_padLatentDistribution]
    constructor
    · rintro ⟨hOldSupport, hNew⟩
      refine ⟨substituteAssignment recipe assignment, hOldSupport, ?_⟩
      exact padJointAssignment_substituteAssignment hSize assignment hNew
    · rintro ⟨oldAssignment, hOldSupport, rfl⟩
      constructor
      · simpa [recipe] using hOldSupport
      · exact newLatentsFalse_padJointAssignment oldAssignment
  · intro assignment hSupport
    rw [support_padLatentDistribution] at hSupport
    rcases hSupport with ⟨oldAssignment, hOldSupport, rfl⟩
    rw [padLatentDistribution_apply_padJointAssignment hSize,
      hLogDensity oldAssignment hOldSupport]
    rw [show paddedTheta.eval (padJointAssignment (larger := larger) oldAssignment) =
        theta.eval (substituteAssignment recipe
          (padJointAssignment (larger := larger) oldAssignment)) by
      simp [paddedTheta]]
    simp [recipe]

/-- Padding preserves local marginality at every positive locality order. -/
theorem isKLocalMarginal_padLatentDistribution
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {smaller larger k : Nat} (hk : 1 ≤ k) (hSize : smaller ≤ larger)
    (joint : Distribution (Assignment (Sum ObsVar (Fin smaller))))
    (hLocal : IsKLocalMarginal k joint) :
    IsKLocalMarginal k (padLatentDistribution (larger := larger) joint) :=
  isKLocalMarginal_of_isFaceGibbs k _
    (isFaceGibbs_padLatentDistribution hk hSize joint
      ((isKLocalMarginal_iff_isFaceGibbs k joint).1 hLocal))

/-- Add unused fixed-false latent bits to a localization. -/
noncomputable def KLocalization.padLatent
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {smaller larger k : Nat} {visible : Distribution (Assignment ObsVar)}
    (localization : KLocalization k ObsVar (Fin smaller) visible)
    (hk : 1 ≤ k) (hSize : smaller ≤ larger) :
    KLocalization k ObsVar (Fin larger) visible where
  lifted := padLatentDistribution (larger := larger) localization.lifted
  marginal := by
    unfold IsMarginalModel padLatentDistribution
    rw [PMF.map_comp]
    rw [show projectObs ∘
        padJointAssignment (ObsVar := ObsVar) (smaller := smaller)
          (larger := larger) = projectObs by
      funext assignment
      exact projectObs_padJointAssignment assignment]
    exact localization.marginal
  kLocal := isKLocalMarginal_padLatentDistribution hk hSize
    localization.lifted localization.kLocal

/-- Existence of a localization is monotone in the permitted latent-bit
count. -/
theorem hasKLocalization_padLatent
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {smaller larger k : Nat} {visible : Distribution (Assignment ObsVar)}
    (hk : 1 ≤ k) (hSize : smaller ≤ larger) :
    HasKLocalization k smaller ObsVar visible →
      HasKLocalization k larger ObsVar visible := by
  rintro ⟨localization⟩
  exact ⟨localization.padLatent hk hSize⟩

theorem hasKLocalizationBits_padLatent
    {n smaller larger k : Nat} {visible : Distribution (BitVec n)}
    (hk : 1 ≤ k) (hSize : smaller ≤ larger) :
    HasKLocalizationBits k smaller n visible →
      HasKLocalizationBits k larger n visible :=
  hasKLocalization_padLatent hk hSize

/-- To prove `budget < LC_k(D)`, it suffices to rule out exactly `budget`
latent bits. -/
theorem localizationComplexity_gt_of_not_hasKLocalization
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {k budget : Nat} (hk : 2 ≤ k)
    (visible : Distribution (Assignment ObsVar))
    (hNoBudget : ¬HasKLocalization k budget ObsVar visible) :
    budget < localizationComplexity k ObsVar visible := by
  have hOptimal := localizationComplexity_spec k ObsVar visible
    (kLocalization_exists visible hk)
  by_contra hNot
  have hAtMost : localizationComplexity k ObsVar visible ≤ budget :=
    Nat.le_of_not_gt hNot
  exact hNoBudget (hasKLocalization_padLatent (by omega) hAtMost hOptimal)

theorem localizationComplexityBits_gt_of_not_hasKLocalization
    {n k budget : Nat} (hk : 2 ≤ k)
    (visible : Distribution (BitVec n))
    (hNoBudget : ¬HasKLocalizationBits k budget n visible) :
    budget < localizationComplexityBits k n visible :=
  localizationComplexity_gt_of_not_hasKLocalization hk visible hNoBudget

end KLocality
