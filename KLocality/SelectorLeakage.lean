import KLocality.FacialClosure

namespace KLocality

universe u v

/-!
# Selector--moment leakage

This module formalizes Theorem `thm:selector-closure` in a form suited to
certified lower bounds.  A selector chooses one latent witness above every
visible support point.  Its graph is safe exactly when the union of supports
in its degree-`k` moment fiber does not project outside the visible support.
-/

/-- Join visible and latent Boolean assignments. -/
def jointAssignment
    {ObsVar : Type u} {LatVar : Type v}
    (visible : Assignment ObsVar) (latent : Assignment LatVar) :
    Assignment (Sum ObsVar LatVar) :=
  Sum.elim visible latent

@[simp]
theorem jointAssignment_apply_observed
    {ObsVar : Type u} {LatVar : Type v}
    (visible : Assignment ObsVar) (latent : Assignment LatVar)
    (coordinate : ObsVar) :
    jointAssignment visible latent (Sum.inl coordinate) = visible coordinate :=
  rfl

@[simp]
theorem jointAssignment_apply_latent
    {ObsVar : Type u} {LatVar : Type v}
    (visible : Assignment ObsVar) (latent : Assignment LatVar)
    (coordinate : LatVar) :
    jointAssignment visible latent (Sum.inr coordinate) = latent coordinate :=
  rfl

@[simp]
theorem projectObs_jointAssignment
    {ObsVar : Type u} {LatVar : Type v}
    (visible : Assignment ObsVar) (latent : Assignment LatVar) :
    projectObs (jointAssignment visible latent) = visible :=
  rfl

/-- Projection to the latent coordinates. -/
def projectLat
    {ObsVar : Type u} {LatVar : Type v}
    (assignment : Assignment (Sum ObsVar LatVar)) : Assignment LatVar :=
  fun coordinate => assignment (Sum.inr coordinate)

@[simp]
theorem projectLat_jointAssignment
    {ObsVar : Type u} {LatVar : Type v}
    (visible : Assignment ObsVar) (latent : Assignment LatVar) :
    projectLat (jointAssignment visible latent) = latent :=
  rfl

@[simp]
theorem jointAssignment_projectObs_projectLat
    {ObsVar : Type u} {LatVar : Type v}
    (assignment : Assignment (Sum ObsVar LatVar)) :
    jointAssignment (projectObs assignment) (projectLat assignment) =
      assignment := by
  funext coordinate
  cases coordinate <;> rfl

/-- A ground-state extension is a degree-`k` facial support whose visible
projection is exactly the requested support. -/
structure GroundStateExtension
    (k : Nat) (ObsVar : Type u) (LatVar : Type v)
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (visibleSupport : Set (Assignment ObsVar)) where
  groundStates : Set (Assignment (Sum ObsVar LatVar))
  facial : IsFacialSupport k groundStates
  projection : projectObs '' groundStates = visibleSupport

/-- Existence of a degree-`k` ground-state extension with the indicated
latent variable type. -/
def HasGroundStateExtension
    (k : Nat) (ObsVar : Type u) (LatVar : Type v)
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (visibleSupport : Set (Assignment ObsVar)) : Prop :=
  Nonempty (GroundStateExtension k ObsVar LatVar visibleSupport)

/-- The support face of a localization is a ground-state extension of the
visible support. -/
def KLocalization.toGroundStateExtension
    {k : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {pObs : Distribution (Assignment ObsVar)}
    (localization : KLocalization k ObsVar LatVar pObs) :
    GroundStateExtension k ObsVar LatVar pObs.support where
  groundStates := localization.lifted.support
  facial := isFacialSupport_of_isKLocalMarginal k localization.lifted
    localization.kLocal
  projection := by
    calc
      projectObs '' localization.lifted.support =
          (localization.lifted.map projectObs).support :=
        (PMF.support_map projectObs localization.lifted).symm
      _ = pObs.support := congrArg (fun p => p.support) localization.marginal

/-- A selector chooses one latent assignment for each point of a finite
visible support. -/
abbrev Selector
    {ObsVar : Type u} (visibleSupport : Finset (Assignment ObsVar))
    (LatVar : Type v) :=
  visibleSupport → Assignment LatVar

/-- The selected joint assignment above one visible support point. -/
def selectorGraphAssignment
    {ObsVar : Type u} {LatVar : Type v}
    {visibleSupport : Finset (Assignment ObsVar)}
    (selector : Selector visibleSupport LatVar)
    (visible : visibleSupport) : Assignment (Sum ObsVar LatVar) :=
  jointAssignment visible.1 (selector visible)

@[simp]
theorem projectObs_selectorGraphAssignment
    {ObsVar : Type u} {LatVar : Type v}
    {visibleSupport : Finset (Assignment ObsVar)}
    (selector : Selector visibleSupport LatVar)
    (visible : visibleSupport) :
    projectObs (selectorGraphAssignment selector visible) = visible.1 :=
  rfl

/-- Uniform law on a selector graph. -/
noncomputable def selectorGraphDistribution
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar) :
    Distribution (Assignment (Sum ObsVar LatVar)) := by
  letI : Nonempty visibleSupport := hVisible.to_subtype
  exact (PMF.uniformOfFintype visibleSupport).map
    (selectorGraphAssignment selector)

theorem support_selectorGraphDistribution
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar) :
    (selectorGraphDistribution hVisible selector).support =
      Set.range (selectorGraphAssignment selector) := by
  letI : Nonempty visibleSupport := hVisible.to_subtype
  rw [selectorGraphDistribution, PMF.support_map,
    PMF.support_uniformOfFintype]
  exact Set.image_univ

theorem selectorGraphAssignment_mem_support
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar)
    (visible : visibleSupport) :
    selectorGraphAssignment selector visible ∈
      (selectorGraphDistribution hVisible selector).support := by
  rw [support_selectorGraphDistribution hVisible selector]
  exact ⟨visible, rfl⟩

theorem not_mem_selectorGraphDistribution_support_of_projectObs_not_mem
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar)
    {joint : Assignment (Sum ObsVar LatVar)}
    (hOutside : projectObs joint ∉ visibleSupport) :
    joint ∉ (selectorGraphDistribution hVisible selector).support := by
  rw [support_selectorGraphDistribution hVisible selector]
  rintro ⟨visible, rfl⟩
  exact hOutside visible.2

/-- The degree-`k` facial closure of a selector graph, represented as its
moment-fiber support union. -/
def selectorFacialClosure
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar) :
    Set (Assignment (Sum ObsVar LatVar)) :=
  momentFacialClosure k (selectorGraphDistribution hVisible selector)

/-- A selector does not leak when every point in its facial closure projects
back into the requested visible support. -/
def SelectorDoesNotLeak
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar) : Prop :=
  ∀ ⦃joint⦄, joint ∈ selectorFacialClosure k hVisible selector →
    projectObs joint ∈ visibleSupport

/-- A selector leaks when a distribution in the same order-`k` moment fiber
puts positive mass above the visible complement. -/
def SelectorLeaks
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar) : Prop :=
  ∃ leakingLaw : Distribution (Assignment (Sum ObsVar LatVar)),
    SameFeatureMomentsUpTo k
      (selectorGraphDistribution hVisible selector) leakingLaw ∧
      ∃ joint ∈ leakingLaw.support, projectObs joint ∉ visibleSupport

/-- Membership in selector facial closure is precisely positive support in
some law with the selector graph's order-`k` moments. -/
theorem mem_selectorFacialClosure_iff_exists_sameMoments
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {visibleSupport : Finset (Assignment ObsVar)}
    {hVisible : visibleSupport.Nonempty}
    {selector : Selector visibleSupport LatVar}
    {joint : Assignment (Sum ObsVar LatVar)} :
    joint ∈ selectorFacialClosure k hVisible selector ↔
      ∃ law : Distribution (Assignment (Sum ObsVar LatVar)),
        SameFeatureMomentsUpTo k
          (selectorGraphDistribution hVisible selector) law ∧
          joint ∈ law.support :=
  Iff.rfl

theorem selectorLeaks_iff_not_doesNotLeak
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar) :
    SelectorLeaks k hVisible selector ↔
      ¬SelectorDoesNotLeak k hVisible selector := by
  classical
  constructor
  · rintro ⟨law, hMoments, joint, hjoint, hOutside⟩ hSafe
    exact hOutside (hSafe ⟨law, hMoments, hjoint⟩)
  · intro hNotSafe
    simp only [SelectorDoesNotLeak] at hNotSafe
    push_neg at hNotSafe
    rcases hNotSafe with ⟨joint, hClosure, hOutside⟩
    rcases hClosure with ⟨law, hMoments, hjoint⟩
    exact ⟨law, hMoments, joint, hjoint, hOutside⟩

/-- **Theorem `thm:selector-closure`, facial-closure part.** A finite support
has a degree-`k` ground-state extension with latent type `LatVar` iff some
selector has no degree-`k` moment leakage. -/
theorem hasGroundStateExtension_iff_exists_selector_doesNotLeak
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) (visibleSupport : Finset (Assignment ObsVar))
    (hVisible : visibleSupport.Nonempty) :
    HasGroundStateExtension k ObsVar LatVar
        (visibleSupport : Set (Assignment ObsVar)) ↔
      ∃ selector : Selector visibleSupport LatVar,
        SelectorDoesNotLeak k hVisible selector := by
  classical
  constructor
  · rintro ⟨extension⟩
    have hWitness (visible : visibleSupport) :
        ∃ joint ∈ extension.groundStates,
          projectObs joint = visible.1 := by
      have hx : visible.1 ∈
          projectObs '' extension.groundStates := by
        rw [extension.projection]
        exact visible.2
      rcases hx with ⟨joint, hJoint, hProjection⟩
      exact ⟨joint, hJoint, hProjection⟩
    let chosenJoint (visible : visibleSupport) :
        Assignment (Sum ObsVar LatVar) :=
      Classical.choose (hWitness visible)
    have chosenJoint_mem (visible : visibleSupport) :
        chosenJoint visible ∈ extension.groundStates :=
      (Classical.choose_spec (hWitness visible)).1
    have chosenJoint_project (visible : visibleSupport) :
        projectObs (chosenJoint visible) = visible.1 :=
      (Classical.choose_spec (hWitness visible)).2
    let selector : Selector visibleSupport LatVar :=
      fun visible => projectLat (chosenJoint visible)
    have graph_eq_chosen (visible : visibleSupport) :
        selectorGraphAssignment selector visible = chosenJoint visible := by
      funext coordinate
      cases coordinate with
      | inl observed =>
          exact congrFun (chosenJoint_project visible).symm observed
      | inr latent => rfl
    have hGraphSupport :
        (selectorGraphDistribution hVisible selector).support ⊆
          extension.groundStates := by
      rw [support_selectorGraphDistribution hVisible selector]
      rintro _ ⟨visible, rfl⟩
      rw [graph_eq_chosen visible]
      exact chosenJoint_mem visible
    refine ⟨selector, ?_⟩
    intro joint hClosure
    have hGround : joint ∈ extension.groundStates :=
      momentFacialClosure_minimal extension.facial hGraphSupport hClosure
    have hProjected : projectObs joint ∈
        projectObs '' extension.groundStates := ⟨joint, hGround, rfl⟩
    rw [extension.projection] at hProjected
    exact hProjected
  · rintro ⟨selector, hSafe⟩
    let graphLaw := selectorGraphDistribution hVisible selector
    let closure := selectorFacialClosure k hVisible selector
    refine ⟨{
      groundStates := closure
      facial := momentFacialClosure_isFacial k graphLaw
      projection := ?_ }⟩
    apply Set.Subset.antisymm
    · intro visible hVisibleImage
      rcases hVisibleImage with ⟨joint, hClosure, rfl⟩
      exact hSafe hClosure
    · intro visible hVisibleMem
      let indexedVisible : visibleSupport := ⟨visible, hVisibleMem⟩
      let joint := selectorGraphAssignment selector indexedVisible
      have hGraph : joint ∈ graphLaw.support :=
        selectorGraphAssignment_mem_support hVisible selector indexedVisible
      have hClosure : joint ∈ closure :=
        support_subset_momentFacialClosure k graphLaw hGraph
      refine ⟨joint, hClosure, ?_⟩
      exact projectObs_selectorGraphAssignment selector indexedVisible

/-- **Theorem `thm:selector-closure`, leakage form.** Failure of a fixed-size
ground-state extension is equivalent to moment leakage for every selector. -/
theorem noGroundStateExtension_iff_every_selector_leaks
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) (visibleSupport : Finset (Assignment ObsVar))
    (hVisible : visibleSupport.Nonempty) :
    (¬HasGroundStateExtension k ObsVar LatVar
        (visibleSupport : Set (Assignment ObsVar))) ↔
      ∀ selector : Selector visibleSupport LatVar,
        SelectorLeaks k hVisible selector := by
  rw [hasGroundStateExtension_iff_exists_selector_doesNotLeak
    k visibleSupport hVisible]
  constructor
  · intro hNo selector
    apply (selectorLeaks_iff_not_doesNotLeak k hVisible selector).2
    intro hSafe
    exact hNo ⟨selector, hSafe⟩
  · intro hLeaks hExists
    rcases hExists with ⟨selector, hSafe⟩
    exact (selectorLeaks_iff_not_doesNotLeak k hVisible selector).1
      (hLeaks selector) hSafe

/-- Universal selector leakage rules out a `k`-localization with this exact
latent variable type. -/
theorem everySelectorLeaks_obstructs_localization
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) (visibleSupport : Finset (Assignment ObsVar))
    (hVisible : visibleSupport.Nonempty)
    (p : Distribution (Assignment ObsVar))
    (hpSupport : p.support = (visibleSupport : Set (Assignment ObsVar)))
    (hLeaks : ∀ selector : Selector visibleSupport LatVar,
      SelectorLeaks k hVisible selector) :
    ¬Nonempty (KLocalization k ObsVar LatVar p) := by
  intro hLocalization
  rcases hLocalization with ⟨localization⟩
  have hExtension : HasGroundStateExtension k ObsVar LatVar
      (visibleSupport : Set (Assignment ObsVar)) := by
    let extension := localization.toGroundStateExtension
    exact ⟨{
      groundStates := extension.groundStates
      facial := extension.facial
      projection := extension.projection.trans hpSupport }⟩
  exact ((noGroundStateExtension_iff_every_selector_leaks
    k visibleSupport hVisible).2 hLeaks) hExtension

end KLocality
