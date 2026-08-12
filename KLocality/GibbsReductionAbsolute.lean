import KLocality.GibbsReductionComposition

namespace KLocality

universe u v w

/-!
# Absolute Gibbs reductions

This file identifies reductions from the zero-coordinate law with ordinary
localizations.  It proves the absolute clause of the Gibbs-reduction calculus
and supplies unconditional existence for `k ≥ 2`.
-/

/-- A relative extension of the zero-coordinate law is an ordinary
face--Gibbs law. -/
theorem isFaceGibbs_of_unitRelative
    {Fresh : Type u} [Fintype Fresh] [DecidableEq Fresh]
    {k : Nat}
    {extension : Distribution (Assignment (Sum (Fin 0) Fresh))}
    (relative : RelativeFaceGibbsCertificate k unitDistribution extension) :
    IsFaceGibbs k extension := by
  refine ⟨⟨relative.energy, relative.energy_nonnegative, ?_⟩,
    relative.potential, ?_⟩
  · intro assignment
    rw [relative.mem_support_iff]
    have hSource : projectObs assignment ∈ unitDistribution.support := by
      rw [PMF.mem_support_iff, unitDistribution_apply]
      exact one_ne_zero
    simp only [hSource, true_and]
  · intro assignment hAssignment
    have hLog := relative.log_probability_eq assignment hAssignment
    simpa [unitDistribution_apply] using hLog

/-- Conversely, an ordinary face--Gibbs law is relative Gibbs over the
zero-coordinate base law. -/
noncomputable def unitRelativeCertificateOfIsFaceGibbs
    {Fresh : Type u} [Fintype Fresh] [DecidableEq Fresh]
    {k : Nat}
    (extension : Distribution (Assignment (Sum (Fin 0) Fresh)))
    (hFaceGibbs : IsFaceGibbs k extension) :
    RelativeFaceGibbsCertificate k unitDistribution extension := by
  classical
  let energy := Classical.choose hFaceGibbs.1
  have hEnergySpec := Classical.choose_spec hFaceGibbs.1
  let potential := Classical.choose hFaceGibbs.2
  have hPotentialSpec := Classical.choose_spec hFaceGibbs.2
  refine {
    energy := energy
    energy_nonnegative := hEnergySpec.1
    potential := potential
    probability_eq := ?_ }
  intro assignment
  rw [unitDistribution_apply, one_mul]
  by_cases hEnergyZero : energy.eval assignment = 0
  · rw [relativeGibbsFactor, if_pos hEnergyZero]
    have hAssignment : assignment ∈ extension.support :=
      (hEnergySpec.2 assignment).1 hEnergyZero
    have hPositive : 0 < (extension assignment).toReal :=
      ENNReal.toReal_pos
        ((PMF.mem_support_iff extension assignment).1 hAssignment)
      (extension.apply_ne_top assignment)
    apply (ENNReal.toReal_eq_toReal_iff'
      (extension.apply_ne_top assignment) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    calc
      (extension assignment).toReal =
          Real.exp (Real.log (extension assignment).toReal) :=
        (Real.exp_log hPositive).symm
      _ = Real.exp (potential.eval assignment) := by
        rw [hPotentialSpec assignment hAssignment]
  · rw [relativeGibbsFactor, if_neg hEnergyZero]
    have hNotSupport : assignment ∉ extension.support := by
      intro hAssignment
      exact hEnergyZero ((hEnergySpec.2 assignment).2 hAssignment)
    exact (extension.apply_eq_zero_iff assignment).2 hNotSupport

/-- Every law reduces to the zero-coordinate law with no fresh coordinates. -/
noncomputable def GibbsReductionWitness.toUnit
    {Source : Type u} [Fintype Source] [DecidableEq Source]
    (k : Nat) (source : Distribution (Assignment Source)) :
    GibbsReductionWitness k Source (Fin 0) source unitDistribution 0 where
  extension := sourceOnlyExtension source
  relative := sourceOnlyRelativeCertificate k source
  designation := ⟨fun target => Fin.elim0 target, fun target => Fin.elim0 target⟩
  marginal := by
    apply PMF.ext
    intro assignment
    rw [PMF.map_apply, unitDistribution_apply]
    have hProjection : ∀ sourceAssignment,
        assignment = projectAlong
          (⟨fun target => Fin.elim0 target,
            fun target => Fin.elim0 target⟩ :
            Fin 0 ↪ Sum Source (Fin 0)) sourceAssignment := by
      intro sourceAssignment
      exact Subsingleton.elim _ _
    simp_rw [if_pos (hProjection _)]
    exact (sourceOnlyExtension source).tsum_coe

theorem hasGibbsReduction_toUnit
    {Source : Type u} [Fintype Source] [DecidableEq Source]
    (k : Nat) (source : Distribution (Assignment Source)) :
    HasGibbsReduction k 0 Source (Fin 0) source unitDistribution :=
  ⟨GibbsReductionWitness.toUnit k source⟩

/-- Reindex an ordinary observed-plus-latent cube as the fresh block of an
absolute reduction. -/
def absoluteVariableEquiv (observed latent : Nat) :
    Sum (Fin observed) (Fin latent) ≃
      Sum (Fin 0) (Fin (observed + latent)) :=
  finSumFinEquiv.trans (Equiv.emptySum (Fin 0) (Fin (observed + latent))).symm

@[simp]
theorem projectAlong_absoluteDesignation_assignmentEquiv
    (observed latent : Nat)
    (assignment : Assignment (Sum (Fin observed) (Fin latent))) :
    projectAlong
        (⟨fun coordinate => absoluteVariableEquiv observed latent (Sum.inl coordinate),
          fun _ _ h => Sum.inl_injective
            ((absoluteVariableEquiv observed latent).injective h)⟩ :
          Fin observed ↪ Sum (Fin 0) (Fin (observed + latent)))
        (assignmentEquiv (absoluteVariableEquiv observed latent) assignment) =
      projectObs assignment := by
  funext coordinate
  simp [projectAlong, projectObs]

/-- Turn a concrete localization into a reduction from the zero-coordinate
law, charging all observed and latent coordinates as fresh. -/
noncomputable def GibbsReductionWitness.ofKLocalization
    {k observed latent : Nat}
    {target : Distribution (Assignment (Fin observed))}
    (localization : KLocalization k (Fin observed) (Fin latent) target) :
    GibbsReductionWitness k (Fin 0) (Fin observed)
      unitDistribution target (observed + latent) := by
  classical
  let variableEquiv := absoluteVariableEquiv observed latent
  let extension := reindexDistribution variableEquiv localization.lifted
  have hFaceGibbs : IsFaceGibbs k extension :=
    isFaceGibbs_reindexDistribution variableEquiv k localization.lifted
      ((isKLocalMarginal_iff_isFaceGibbs k localization.lifted).1
        localization.kLocal)
  let designation : Fin observed ↪
      Sum (Fin 0) (Fin (observed + latent)) :=
    ⟨fun coordinate => variableEquiv (Sum.inl coordinate),
      fun _ _ h => Sum.inl_injective (variableEquiv.injective h)⟩
  refine {
    extension := extension
    relative := unitRelativeCertificateOfIsFaceGibbs extension hFaceGibbs
    designation := designation
    marginal := ?_ }
  unfold extension reindexDistribution
  rw [PMF.map_comp]
  have hProjection : projectAlong designation ∘
      assignmentEquiv variableEquiv = projectObs := by
    funext assignment
    exact projectAlong_absoluteDesignation_assignmentEquiv observed latent assignment
  rw [hProjection]
  exact localization.marginal

/-- An `ℓ`-bit localization gives an absolute Gibbs reduction of cost
`n + ℓ`. -/
theorem hasGibbsReduction_unit_of_hasKLocalization
    {k observed latent : Nat}
    {target : Distribution (Assignment (Fin observed))}
    (hLocalization : HasKLocalization k latent (Fin observed) target) :
    HasGibbsReduction k (observed + latent) (Fin 0) (Fin observed)
      unitDistribution target := by
  rcases hLocalization with ⟨localization⟩
  exact ⟨GibbsReductionWitness.ofKLocalization localization⟩

/-- The designated coordinates are equivalent to the range subtype. -/
noncomputable def designationRangeEquiv
    {Target Ambient : Type u} [Fintype Target] [Fintype Ambient]
    [DecidableEq Target] [DecidableEq Ambient]
    (designation : Target ↪ Ambient) :
    Target ≃ {coordinate : Ambient // coordinate ∈ Set.range designation} :=
  Equiv.ofInjective designation designation.injective

/-- Cardinality of the complement of an `n`-coordinate designation in an
absolute `cost`-coordinate cube. -/
theorem absoluteDesignation_complement_card
    {observed cost : Nat}
    (designation : Fin observed ↪ Sum (Fin 0) (Fin cost)) :
    Fintype.card
        {coordinate : Sum (Fin 0) (Fin cost) //
          coordinate ∉ Set.range designation} =
      cost - observed := by
  classical
  rw [Fintype.card_subtype_compl]
  have hRange : Fintype.card
      {coordinate : Sum (Fin 0) (Fin cost) //
        coordinate ∈ Set.range designation} = observed := by
    simpa using (Fintype.card_congr (designationRangeEquiv designation)).symm
  rw [hRange]
  simp

/-- Identify `Fin (cost - observed)` with the undesignated coordinates. -/
noncomputable def absoluteDesignationComplementEquiv
    {observed cost : Nat}
    (designation : Fin observed ↪ Sum (Fin 0) (Fin cost)) :
    Fin (cost - observed) ≃
      {coordinate : Sum (Fin 0) (Fin cost) //
        coordinate ∉ Set.range designation} :=
  (finCongr (absoluteDesignation_complement_card designation).symm).trans
    (Fintype.equivFin _).symm

/-- Split an arbitrary output designation into observed coordinates and its
finite complement.  On the observed summand this equivalence is exactly the
given designation. -/
noncomputable def absoluteDesignationSplitEquiv
    {observed cost : Nat}
    (designation : Fin observed ↪ Sum (Fin 0) (Fin cost)) :
    Sum (Fin observed) (Fin (cost - observed)) ≃
      Sum (Fin 0) (Fin cost) := by
  classical
  exact (Equiv.sumCongr (designationRangeEquiv designation)
      (absoluteDesignationComplementEquiv designation)).trans
    (Equiv.sumCompl fun coordinate => coordinate ∈ Set.range designation)

@[simp]
theorem absoluteDesignationSplitEquiv_apply_inl
    {observed cost : Nat}
    (designation : Fin observed ↪ Sum (Fin 0) (Fin cost))
    (coordinate : Fin observed) :
    absoluteDesignationSplitEquiv designation (Sum.inl coordinate) =
      designation coordinate := by
  classical
  rfl

@[simp]
theorem projectObs_assignmentEquiv_absoluteDesignationSplit
    {observed cost : Nat}
    (designation : Fin observed ↪ Sum (Fin 0) (Fin cost))
    (assignment : Assignment (Sum (Fin 0) (Fin cost))) :
    projectObs
        (assignmentEquiv (absoluteDesignationSplitEquiv designation).symm
          assignment) =
      projectAlong designation assignment := by
  funext coordinate
  simp [projectObs, projectAlong]

/-- Every absolute reduction of cost `r` induces a localization using the
`r - n` undesignated coordinates as latent bits. -/
noncomputable def KLocalization.ofUnitGibbsReduction
    {k observed cost : Nat}
    {target : Distribution (Assignment (Fin observed))}
    (reduction : GibbsReductionWitness k (Fin 0) (Fin observed)
      unitDistribution target cost) :
    KLocalization k (Fin observed) (Fin (cost - observed)) target := by
  classical
  let split := absoluteDesignationSplitEquiv reduction.designation
  let joint := reindexDistribution split.symm reduction.extension
  refine {
    lifted := joint
    marginal := ?_
    kLocal := ?_ }
  · unfold joint reindexDistribution
    unfold IsMarginalModel
    rw [PMF.map_comp]
    have hProjection : projectObs ∘ assignmentEquiv split.symm =
        projectAlong reduction.designation := by
      funext assignment
      exact projectObs_assignmentEquiv_absoluteDesignationSplit
        reduction.designation assignment
    rw [hProjection]
    exact reduction.marginal
  · exact (isKLocalMarginal_reindexDistribution_iff split.symm k
      reduction.extension).2
      (isKLocalMarginal_of_isFaceGibbs k reduction.extension
        (isFaceGibbs_of_unitRelative reduction.relative))

/-- An injection of `n` output coordinates into an absolute cost-`r` cube
forces `n ≤ r`. -/
theorem observed_le_cost_of_unitGibbsReduction
    {k observed cost : Nat}
    {target : Distribution (Assignment (Fin observed))}
    (reduction : GibbsReductionWitness k (Fin 0) (Fin observed)
      unitDistribution target cost) :
    observed ≤ cost := by
  have hCard := Fintype.card_le_of_injective reduction.designation
    reduction.designation.injective
  simpa using hCard

/-- Any absolute reduction pays for all observed coordinates and at least the
optimal latent-coordinate count. -/
theorem observed_add_localizationComplexity_le_of_hasUnitGibbsReduction
    {k observed cost : Nat}
    (target : Distribution (Assignment (Fin observed)))
    (hReduction : HasGibbsReduction k cost (Fin 0) (Fin observed)
      unitDistribution target) :
    observed + localizationComplexity k (Fin observed) target ≤ cost := by
  rcases hReduction with ⟨reduction⟩
  have hLocalization : HasKLocalization k (cost - observed)
      (Fin observed) target :=
    ⟨KLocalization.ofUnitGibbsReduction reduction⟩
  have hMinimum := localizationComplexity_min k (Fin observed) target
    (cost - observed) hLocalization
  have hObserved := observed_le_cost_of_unitGibbsReduction reduction
  omega

/-- **Proposition `prop:gibbs-reduction-calculus`, absolute clause.**  A
reduction from the zero-coordinate law pays once for every observed bit and
then exactly the ordinary localization complexity. -/
theorem gibbsReductionCost_unit_eq
    {k observed : Nat} (hk : 2 ≤ k)
    (target : Distribution (Assignment (Fin observed))) :
    gibbsReductionCost k (Fin 0) (Fin observed) unitDistribution target =
      observed + localizationComplexity k (Fin observed) target := by
  have hLocalizationExists := kLocalization_exists target hk
  have hOptimalLocalization := localizationComplexity_spec k (Fin observed)
    target hLocalizationExists
  have hUpperWitness : HasGibbsReduction k
      (observed + localizationComplexity k (Fin observed) target)
      (Fin 0) (Fin observed) unitDistribution target :=
    hasGibbsReduction_unit_of_hasKLocalization hOptimalLocalization
  have hUpper := gibbsReductionCost_min k (Fin 0) (Fin observed)
    unitDistribution target
    (observed + localizationComplexity k (Fin observed) target) hUpperWitness
  have hReductionExists : ∃ cost,
      HasGibbsReduction k cost (Fin 0) (Fin observed)
        unitDistribution target :=
    ⟨observed + localizationComplexity k (Fin observed) target, hUpperWitness⟩
  have hOptimalReduction := gibbsReductionCost_spec k (Fin 0) (Fin observed)
    unitDistribution target hReductionExists
  have hLower := observed_add_localizationComplexity_le_of_hasUnitGibbsReduction
    target hOptimalReduction
  exact Nat.le_antisymm hUpper hLower

/-- Rename only the target coordinates of a Gibbs reduction. -/
noncomputable def GibbsReductionWitness.reindexTarget
    {Source : Type u} {Target : Type v} {Target' : Type w}
    [Fintype Source] [Fintype Target] [Fintype Target']
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Target']
    {k cost : Nat}
    {source : Distribution (Assignment Source)}
    {target : Distribution (Assignment Target)}
    (reduction : GibbsReductionWitness k Source Target source target cost)
    (equiv : Target ≃ Target') :
    GibbsReductionWitness k Source Target' source
      (reindexDistribution equiv target) cost where
  extension := reduction.extension
  relative := reduction.relative
  designation := equiv.symm.toEmbedding.trans reduction.designation
  marginal := by
    have hProjection : projectAlong
          (equiv.symm.toEmbedding.trans reduction.designation) =
        assignmentEquiv equiv ∘ projectAlong reduction.designation := by
      funext assignment
      rfl
    unfold reindexDistribution
    rw [hProjection, ← PMF.map_comp, reduction.marginal]

/-- Every pair of finite Boolean laws admits a Gibbs reduction when `k ≥ 2`.
The construction first discards the source into the zero-coordinate law and
then uses universal localization of the target. -/
theorem gibbsReduction_exists
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    {k : Nat} (hk : 2 ≤ k)
    (source : Distribution (Assignment Source))
    (target : Distribution (Assignment Target)) :
    ∃ cost, HasGibbsReduction k cost Source Target source target := by
  classical
  let targetEquiv := Fintype.equivFin Target
  let targetFin := reindexDistribution targetEquiv target
  have hLocalizationExists := kLocalization_exists targetFin hk
  let latent := localizationComplexity k (Fin (Fintype.card Target)) targetFin
  rcases localizationComplexity_spec k (Fin (Fintype.card Target)) targetFin
      hLocalizationExists with ⟨localization⟩
  let absoluteReduction := GibbsReductionWitness.ofKLocalization localization
  let renamedReduction := absoluteReduction.reindexTarget targetEquiv.symm
  have hRenamedTarget :
      reindexDistribution targetEquiv.symm targetFin = target := by
    exact reindexDistribution_symm_reindexDistribution targetEquiv target
  have hUnitToTarget : HasGibbsReduction k
      (Fintype.card Target + latent) (Fin 0) Target unitDistribution target := by
    rw [← hRenamedTarget]
    exact ⟨renamedReduction⟩
  have hComposite := hasGibbsReduction_comp
    (Source := Source) (Middle := Fin 0) (Target := Target)
    (first := 0) (second := Fintype.card Target + latent)
    (hasGibbsReduction_toUnit k source) hUnitToTarget
  exact ⟨Fintype.card Target + latent, by simpa using hComposite⟩

/-- **Proposition `prop:gibbs-reduction-calculus`, composition clause.** -/
theorem gibbsReductionCost_comp_le
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k : Nat} (hk : 2 ≤ k)
    (source : Distribution (Assignment Source))
    (middle : Distribution (Assignment Middle))
    (target : Distribution (Assignment Target)) :
    gibbsReductionCost k Source Target source target ≤
      gibbsReductionCost k Source Middle source middle +
        gibbsReductionCost k Middle Target middle target :=
  gibbsReductionCost_comp_le_of_exists source middle target
    (gibbsReduction_exists hk source middle)
    (gibbsReduction_exists hk middle target)

/-- **Corollary `cor:gibbs-reduction-compilation`.** -/
theorem observed_add_localizationComplexity_le_compilation
    {k sourceBits targetBits : Nat} (hk : 2 ≤ k)
    (source : Distribution (Assignment (Fin sourceBits)))
    (target : Distribution (Assignment (Fin targetBits))) :
    targetBits + localizationComplexity k (Fin targetBits) target ≤
      sourceBits + localizationComplexity k (Fin sourceBits) source +
        gibbsReductionCost k (Fin sourceBits) (Fin targetBits) source target := by
  have hComp := gibbsReductionCost_comp_le hk unitDistribution source target
  rw [gibbsReductionCost_unit_eq hk source,
    gibbsReductionCost_unit_eq hk target] at hComp
  exact hComp

/-- The disjoint-output consequence of the compilation corollary.  A witness
of cost `targetBits + workspaceBits` yields the stated hidden-overhead bound;
the theorem in fact does not require the output designation to be disjoint. -/
theorem localizationComplexity_le_of_hasGibbsReduction
    {k sourceBits targetBits workspaceBits : Nat} (hk : 2 ≤ k)
    (source : Distribution (Assignment (Fin sourceBits)))
    (target : Distribution (Assignment (Fin targetBits)))
    (hReduction : HasGibbsReduction k (targetBits + workspaceBits)
      (Fin sourceBits) (Fin targetBits) source target) :
    localizationComplexity k (Fin targetBits) target ≤
      sourceBits + localizationComplexity k (Fin sourceBits) source +
        workspaceBits := by
  have hCompilation :=
    observed_add_localizationComplexity_le_compilation hk source target
  have hCost := gibbsReductionCost_min k (Fin sourceBits) (Fin targetBits)
    source target (targetBits + workspaceBits) hReduction
  omega

end KLocality
