import KLocality.FacialConditioning
import KLocality.CoordinatePullback

namespace KLocality

universe u v w

/-!
# Facial conditioning followed by coordinate pullback

This file proves the second clause of the paper's facial-conditioning lemma.
After conditioning on a facial event, an event parametrization may duplicate
observed coordinates or fix them to constants.  The same substitution is
applied to the observed part of a localization, while its latent coordinates
are left unchanged.
-/

/-- Extend an observed-coordinate recipe to the joint observed/latent cube,
leaving every latent coordinate unchanged. -/
def jointCoordinateRecipe
    {ObsVar : Type u} {TargetVar : Type v} {LatVar : Type w}
    (recipe : ObsVar → CoordinateRecipe TargetVar) :
    Sum ObsVar LatVar → CoordinateRecipe (Sum TargetVar LatVar)
  | Sum.inl observed =>
      match recipe observed with
      | Sum.inl target => Sum.inl (Sum.inl target)
      | Sum.inr value => Sum.inr value
  | Sum.inr latent => Sum.inl (Sum.inr latent)

@[simp]
theorem projectObs_substituteAssignment_jointCoordinateRecipe
    {ObsVar : Type u} {TargetVar : Type v} {LatVar : Type w}
    (recipe : ObsVar → CoordinateRecipe TargetVar)
    (assignment : Assignment (Sum TargetVar LatVar)) :
    projectObs (substituteAssignment (jointCoordinateRecipe recipe) assignment) =
      substituteAssignment recipe (projectObs assignment) := by
  funext observed
  cases hRecipe : recipe observed <;>
    simp [projectObs, substituteAssignment, jointCoordinateRecipe, hRecipe]

@[simp]
theorem substituteAssignment_jointCoordinateRecipe_latent
    {ObsVar : Type u} {TargetVar : Type v} {LatVar : Type w}
    (recipe : ObsVar → CoordinateRecipe TargetVar)
    (assignment : Assignment (Sum TargetVar LatVar)) (latent : LatVar) :
    substituteAssignment (jointCoordinateRecipe recipe) assignment (Sum.inr latent) =
      assignment (Sum.inr latent) := by
  rfl

/-- The joint-cube map induced by an observed event parametrization. -/
def jointParametrizationToFun
    {ObsVar : Type u} {TargetVar : Type v} {LatVar : Type w}
    {event : Set (Assignment ObsVar)}
    (parametrization : CoordinateParametrization ObsVar TargetVar event)
    (assignment : Assignment (Sum TargetVar LatVar)) :
    liftedEvent (LatVar := LatVar) event := by
  refine ⟨substituteAssignment
    (jointCoordinateRecipe parametrization.recipe) assignment, ?_⟩
  change projectObs (substituteAssignment
    (jointCoordinateRecipe parametrization.recipe) assignment) ∈ event
  rw [projectObs_substituteAssignment_jointCoordinateRecipe]
  rw [← parametrization.equiv_apply]
  exact (parametrization.equiv (projectObs assignment)).2

/-- Inverse to the joint-cube map: invert the observed parametrization and
copy latent coordinates verbatim. -/
noncomputable def jointParametrizationInvFun
    {ObsVar : Type u} {TargetVar : Type v} {LatVar : Type w}
    {event : Set (Assignment ObsVar)}
    (parametrization : CoordinateParametrization ObsVar TargetVar event)
    (assignment : liftedEvent (LatVar := LatVar) event) :
    Assignment (Sum TargetVar LatVar)
  | Sum.inl target =>
      parametrization.equiv.symm
        ⟨projectObs assignment.1, assignment.2⟩ target
  | Sum.inr latent => assignment.1 (Sum.inr latent)

/-- An observed duplication/fixing parametrization extends to the joint cube
by preserving all latent coordinates. -/
noncomputable def jointCoordinateParametrization
    {ObsVar : Type u} {TargetVar : Type v} {LatVar : Type w}
    {event : Set (Assignment ObsVar)}
    (parametrization : CoordinateParametrization ObsVar TargetVar event) :
    CoordinateParametrization (Sum ObsVar LatVar) (Sum TargetVar LatVar)
      (liftedEvent (LatVar := LatVar) event) where
  recipe := jointCoordinateRecipe parametrization.recipe
  equiv := {
    toFun := jointParametrizationToFun parametrization
    invFun := jointParametrizationInvFun parametrization
    left_inv := by
      intro assignment
      funext coordinate
      cases coordinate with
      | inl target =>
          let observed : event :=
            ⟨projectObs (jointParametrizationToFun parametrization assignment).1,
              (jointParametrizationToFun parametrization assignment).2⟩
          have hSubtype :
              observed =
                parametrization.equiv (projectObs assignment) := by
            apply Subtype.ext
            change projectObs
                (substituteAssignment
                  (jointCoordinateRecipe parametrization.recipe) assignment) =
              (parametrization.equiv (projectObs assignment)).1
            rw [projectObs_substituteAssignment_jointCoordinateRecipe,
              ← parametrization.equiv_apply]
          change parametrization.equiv.symm observed target =
            assignment (Sum.inl target)
          rw [hSubtype, parametrization.equiv.symm_apply_apply]
          rfl
      | inr latent => rfl
    right_inv := by
      intro assignment
      apply Subtype.ext
      change substituteAssignment
          (jointCoordinateRecipe parametrization.recipe)
          (jointParametrizationInvFun parametrization assignment) = assignment.1
      have hObserved :
          projectObs
              (substituteAssignment
                (jointCoordinateRecipe parametrization.recipe)
                (jointParametrizationInvFun parametrization assignment)) =
            projectObs assignment.1 := by
        rw [projectObs_substituteAssignment_jointCoordinateRecipe]
        change substituteAssignment parametrization.recipe
            (parametrization.equiv.symm
              ⟨projectObs assignment.1, assignment.2⟩) =
          projectObs assignment.1
        rw [← parametrization.equiv_apply]
        exact congrArg Subtype.val (parametrization.equiv.apply_symm_apply
          ⟨projectObs assignment.1, assignment.2⟩)
      funext coordinate
      cases coordinate with
      | inl observed =>
          exact congrFun hObserved observed
      | inr latent => rfl }
  equiv_apply := by
    intro assignment
    rfl

@[simp]
theorem jointCoordinateParametrization_projectObs
    {ObsVar : Type u} {TargetVar : Type v} {LatVar : Type w}
    {event : Set (Assignment ObsVar)}
    (parametrization : CoordinateParametrization ObsVar TargetVar event)
    (assignment : Assignment (Sum TargetVar LatVar)) :
    projectObs ((jointCoordinateParametrization
      (LatVar := LatVar) parametrization).equiv assignment).1 =
      (parametrization.equiv (projectObs assignment)).1 := by
  rw [(jointCoordinateParametrization
      (LatVar := LatVar) parametrization).equiv_apply]
  change projectObs
      (substituteAssignment
        (jointCoordinateRecipe parametrization.recipe) assignment) = _
  rw [
    projectObs_substituteAssignment_jointCoordinateRecipe,
    ← parametrization.equiv_apply]

/-- The support of a filtered law lies in the filtering event. -/
theorem support_filter_subset_event
    {Alpha : Type u} (p : Distribution Alpha) (event : Set Alpha)
    (hPositive : HasPositiveSupportIntersection p event) :
    (p.filter event hPositive).support ⊆ event := by
  intro value hValue
  exact ((PMF.mem_support_filter_iff hPositive).1 hValue).1

/-- Condition on an observed event and then transport the resulting law to
the event's duplication/fixing coordinates. -/
noncomputable def facialConditionalPullback
    {ObsVar : Type u} {TargetVar : Type v}
    [Fintype ObsVar] [Fintype TargetVar]
    (p : Distribution (Assignment ObsVar))
    (event : Set (Assignment ObsVar))
    (hPositive : HasPositiveSupportIntersection p event)
    (parametrization : CoordinateParametrization ObsVar TargetVar event) :
    Distribution (Assignment TargetVar) :=
  pullbackDistribution (p.filter event hPositive)
    (support_filter_subset_event p event hPositive) parametrization

@[simp]
theorem facialConditionalPullback_apply
    {ObsVar : Type u} {TargetVar : Type v}
    [Fintype ObsVar] [Fintype TargetVar]
    (p : Distribution (Assignment ObsVar))
    (event : Set (Assignment ObsVar))
    (hPositive : HasPositiveSupportIntersection p event)
    (parametrization : CoordinateParametrization ObsVar TargetVar event)
    (assignment : Assignment TargetVar) :
    facialConditionalPullback p event hPositive parametrization assignment =
      p.filter event hPositive (parametrization.equiv assignment).1 := by
  rfl

/-- A localization survives facial conditioning and the paper's subsequent
coordinate operation (deleting fixed coordinates and identifying duplicated
ones), with exactly the same latent-variable type. -/
noncomputable def KLocalization.filterFacialPullback
    {ObsVar : Type u} {LatVar : Type v} {TargetVar : Type w}
    [Fintype ObsVar] [Fintype LatVar] [Fintype TargetVar]
    [DecidableEq ObsVar] [DecidableEq LatVar] [DecidableEq TargetVar]
    {k : Nat} {pObs : Distribution (Assignment ObsVar)}
    (localization : KLocalization k ObsVar LatVar pObs)
    (event : Set (Assignment ObsVar))
    (hPositive : HasPositiveSupportIntersection pObs event)
    (hFacial : IsFacialSupport k event)
    (parametrization : CoordinateParametrization ObsVar TargetVar event) :
    KLocalization k TargetVar LatVar
      (facialConditionalPullback pObs event hPositive parametrization) := by
  classical
  have hJointPositive : HasPositiveSupportIntersection localization.lifted
      (liftedEvent (LatVar := LatVar) event) :=
    exists_support_lift_of_isMarginalModel pObs localization.lifted
      localization.marginal event hPositive
  let conditioned := localization.filterFacial event hPositive hFacial
  have hJointSupport : conditioned.lifted.support ⊆
      liftedEvent (LatVar := LatVar) event := by
    intro assignment hAssignment
    change assignment ∈
      (localization.lifted.filter
        (liftedEvent (LatVar := LatVar) event) hJointPositive).support at hAssignment
    exact ((PMF.mem_support_filter_iff _).1 hAssignment).1
  let jointParametrization :=
    jointCoordinateParametrization (LatVar := LatVar) parametrization
  let pulledJoint := pullbackDistribution conditioned.lifted hJointSupport
    jointParametrization
  refine {
    lifted := pulledJoint
    marginal := ?_
    kLocal := ?_ }
  · dsimp only [pulledJoint]
    exact map_pullbackDistribution
      conditioned.lifted (pObs.filter event hPositive)
      hJointSupport (support_filter_subset_event pObs event hPositive)
      jointParametrization parametrization projectObs projectObs
      conditioned.marginal
      (jointCoordinateParametrization_projectObs
        (LatVar := LatVar) parametrization)
  · dsimp only [pulledJoint]
    exact isKLocalMarginal_pullbackDistribution conditioned.lifted
      hJointSupport jointParametrization conditioned.kLocal

/-- **Lemma `lem:facial-conditioning`, full statement.** Conditioning on a
positive degree-`k` facial event and then deleting fixed coordinates or
identifying duplicated coordinates cannot increase localization complexity. -/
theorem localizationComplexity_facialConditionalPullback_le
    {ObsVar : Type u} {TargetVar : Type v}
    [Fintype ObsVar] [Fintype TargetVar]
    [DecidableEq ObsVar] [DecidableEq TargetVar]
    {k : Nat} (hk : 2 ≤ k)
    (p : Distribution (Assignment ObsVar))
    (event : Set (Assignment ObsVar))
    (hPositive : HasPositiveSupportIntersection p event)
    (hFacial : IsFacialSupport k event)
    (parametrization : CoordinateParametrization ObsVar TargetVar event) :
    localizationComplexity k TargetVar
        (facialConditionalPullback p event hPositive parametrization) ≤
      localizationComplexity k ObsVar p := by
  let latentVars := localizationComplexity k ObsVar p
  rcases localizationComplexity_spec k ObsVar p (kLocalization_exists p hk) with
    ⟨localization⟩
  apply localizationComplexity_min
  exact ⟨localization.filterFacialPullback event hPositive hFacial
    parametrization⟩

end KLocality
