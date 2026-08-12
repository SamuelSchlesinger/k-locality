import KLocality.RelativeGibbs

namespace KLocality

universe u v

/-!
# Gibbs reductions

Fresh coordinates are represented canonically by `Fin cost`.  Target
coordinates may be any injectively designated coordinates of the
source-plus-fresh cube, exactly as in Definition `def:gibbs-reduction`.
-/

/-- Restrict an assignment along an injective designation of coordinates. -/
def projectAlong
    {Target : Type u} {Ambient : Type v}
    (designation : Target ↪ Ambient)
    (assignment : Assignment Ambient) : Assignment Target :=
  fun target => assignment (designation target)

/-- The unique assignment on the zero-coordinate cube. -/
def emptyAssignment : Assignment (Fin 0) :=
  fun coordinate => Fin.elim0 coordinate

/-- `1`, the unique distribution on the zero-coordinate cube. -/
noncomputable def unitDistribution : Distribution (Assignment (Fin 0)) :=
  PMF.pure emptyAssignment

@[simp]
theorem unitDistribution_apply (assignment : Assignment (Fin 0)) :
    unitDistribution assignment = 1 := by
  have hAssignment : assignment = emptyAssignment := Subsingleton.elim _ _
  subst assignment
  simp [unitDistribution]

/-- Rename source coordinates into the source-plus-zero-fresh cube. -/
def sourceOnlyVariableEquiv (Source : Type u) :
    Source ≃ Sum Source (Fin 0) :=
  (Equiv.sumEmpty Source (Fin 0)).symm

@[simp]
theorem projectObs_assignmentEquiv_sourceOnly
    {Source : Type u} (assignment : Assignment Source) :
    projectObs (assignmentEquiv (sourceOnlyVariableEquiv Source) assignment) =
      assignment := by
  rfl

@[simp]
theorem assignmentEquiv_sourceOnly_projectObs
    {Source : Type u} (assignment : Assignment (Sum Source (Fin 0))) :
    assignmentEquiv (sourceOnlyVariableEquiv Source) (projectObs assignment) =
      assignment := by
  funext coordinate
  cases coordinate with
  | inl source => rfl
  | inr fresh => exact Fin.elim0 fresh

/-- The source law itself, viewed as an extension with no fresh coordinates. -/
noncomputable def sourceOnlyExtension
    {Source : Type u} (source : Distribution (Assignment Source)) :
    Distribution (Assignment (Sum Source (Fin 0))) :=
  reindexDistribution (sourceOnlyVariableEquiv Source) source

@[simp]
theorem sourceOnlyExtension_apply
    {Source : Type u} (source : Distribution (Assignment Source))
    (assignment : Assignment (Sum Source (Fin 0))) :
    sourceOnlyExtension source assignment = source (projectObs assignment) := by
  rw [show assignment = assignmentEquiv (sourceOnlyVariableEquiv Source)
      (projectObs assignment) by
    symm
    exact assignmentEquiv_sourceOnly_projectObs assignment]
  exact reindexDistribution_apply_assignmentEquiv _ _ _

/-- A concrete cost-`cost` relative Gibbs reduction. -/
structure GibbsReductionWitness
    (k : Nat)
    (Source : Type u) (Target : Type v)
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (source : Distribution (Assignment Source))
    (target : Distribution (Assignment Target))
    (cost : Nat) where
  extension : Distribution (Assignment (Sum Source (Fin cost)))
  relative : RelativeFaceGibbsCertificate k source extension
  designation : Target ↪ Sum Source (Fin cost)
  marginal : extension.map (projectAlong designation) = target

/-- Existence of a relative Gibbs reduction with exactly `cost` fresh bits. -/
def HasGibbsReduction
    (k cost : Nat)
    (Source : Type u) (Target : Type v)
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (source : Distribution (Assignment Source))
    (target : Distribution (Assignment Target)) : Prop :=
  Nonempty (GibbsReductionWitness k Source Target source target cost)

/-- The minimum fresh-coordinate cost, with a total fallback before universal
existence is established. -/
noncomputable def gibbsReductionCost
    (k : Nat)
    (Source : Type u) (Target : Type v)
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (source : Distribution (Assignment Source))
    (target : Distribution (Assignment Target)) : Nat := by
  classical
  exact if hExists : ∃ cost,
      HasGibbsReduction k cost Source Target source target then
    Nat.find hExists
  else 0

theorem gibbsReductionCost_spec
    (k : Nat)
    (Source : Type u) (Target : Type v)
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (source : Distribution (Assignment Source))
    (target : Distribution (Assignment Target))
    (hExists : ∃ cost,
      HasGibbsReduction k cost Source Target source target) :
    HasGibbsReduction k
      (gibbsReductionCost k Source Target source target)
      Source Target source target := by
  classical
  simp only [gibbsReductionCost, dif_pos hExists]
  exact Nat.find_spec hExists

theorem gibbsReductionCost_min
    (k : Nat)
    (Source : Type u) (Target : Type v)
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (source : Distribution (Assignment Source))
    (target : Distribution (Assignment Target))
    (cost : Nat)
    (hReduction : HasGibbsReduction k cost Source Target source target) :
    gibbsReductionCost k Source Target source target ≤ cost := by
  classical
  let hExists : ∃ cost,
      HasGibbsReduction k cost Source Target source target := ⟨cost, hReduction⟩
  simp only [gibbsReductionCost, dif_pos hExists]
  exact Nat.find_min' hExists hReduction

/-- The zero-fresh-coordinate extension is relative Gibbs with zero energy
and zero potential. -/
noncomputable def sourceOnlyRelativeCertificate
    {Source : Type u} [Fintype Source] [DecidableEq Source]
    (k : Nat) (source : Distribution (Assignment Source)) :
    RelativeFaceGibbsCertificate k source (sourceOnlyExtension source) where
  energy := 0
  energy_nonnegative := by
    intro assignment
    simp [FeaturePolynomial.eval]
  potential := 0
  probability_eq := by
    intro assignment
    rw [sourceOnlyExtension_apply]
    simp [relativeGibbsFactor, FeaturePolynomial.eval]

/-- Identity Gibbs reduction, with no fresh coordinates. -/
noncomputable def GibbsReductionWitness.identity
    {Source : Type u} [Fintype Source] [DecidableEq Source]
    (k : Nat) (source : Distribution (Assignment Source)) :
    GibbsReductionWitness k Source Source source source 0 where
  extension := sourceOnlyExtension source
  relative := sourceOnlyRelativeCertificate k source
  designation := ⟨Sum.inl, Sum.inl_injective⟩
  marginal := by
    unfold sourceOnlyExtension reindexDistribution
    rw [PMF.map_comp]
    have hComp : projectAlong (⟨Sum.inl, Sum.inl_injective⟩ :
        Source ↪ Sum Source (Fin 0)) ∘
          assignmentEquiv (sourceOnlyVariableEquiv Source) = id := by
      funext assignment
      rfl
    rw [hComp, PMF.map_id]

/-- **Proposition `prop:gibbs-reduction-calculus`, identity clause.** -/
theorem gibbsReductionCost_self
    {Source : Type u} [Fintype Source] [DecidableEq Source]
    (k : Nat) (source : Distribution (Assignment Source)) :
    gibbsReductionCost k Source Source source source = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact gibbsReductionCost_min k Source Source source source 0
    ⟨GibbsReductionWitness.identity k source⟩

end KLocality
