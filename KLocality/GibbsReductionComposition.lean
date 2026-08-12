import KLocality.GibbsReduction

namespace KLocality

open scoped BigOperators

universe u v w

/-!
# Composition of Gibbs reductions

The proofs below use a canonical split of `Fin (a + b)` into the first `a`
and last `b` fresh coordinates.  This makes the finite-sum argument underlying
composition explicit.
-/

/-- Pulling a finite PMF forward transports expectations of arbitrary
`ENNReal` weights. -/
theorem sum_probability_mul_of_map
    {Alpha : Type u} {Beta : Type v}
    [Fintype Alpha] [Fintype Beta]
    (p : Distribution Alpha) (q : Distribution Beta)
    (map : Alpha → Beta) (hMap : p.map map = q)
    (weight : Beta → ENNReal) :
    ∑ alpha, p alpha * weight (map alpha) =
      ∑ beta, q beta * weight beta := by
  classical
  rw [← hMap]
  simp only [PMF.map_apply, tsum_fintype]
  symm
  calc
    ∑ beta, (∑ alpha, if beta = map alpha then p alpha else 0) * weight beta =
        ∑ beta, ∑ alpha,
          (if beta = map alpha then p alpha else 0) * weight beta := by
      apply Finset.sum_congr rfl
      intro beta _
      rw [Finset.sum_mul]
    _ = ∑ alpha, ∑ beta,
        (if beta = map alpha then p alpha else 0) * weight beta :=
      Finset.sum_comm
    _ = ∑ alpha, p alpha * weight (map alpha) := by
      apply Finset.sum_congr rfl
      intro alpha _
      rw [Fintype.sum_eq_single (map alpha)]
      · simp
      · intro beta hBeta
        simp [hBeta]

/-- Split an appended block of fresh coordinates. -/
def splitFreshVariableEquiv (Source : Type u) (first second : Nat) :
    Sum Source (Fin (first + second)) ≃
      Sum (Sum Source (Fin first)) (Fin second) :=
  (Equiv.sumCongr (Equiv.refl Source) finSumFinEquiv.symm).trans
    (Equiv.sumAssoc Source (Fin first) (Fin second)).symm

/-- Split a joint assignment into its old source-plus-first-fresh assignment
and its second block of fresh bits. -/
def splitFreshAssignmentEquiv (Source : Type u) (first second : Nat) :
    Assignment (Sum Source (Fin (first + second))) ≃
      Assignment (Sum Source (Fin first)) × Assignment (Fin second) :=
  (assignmentEquiv (splitFreshVariableEquiv Source first second)).trans
    (Equiv.sumArrowEquivProdArrow (Sum Source (Fin first)) (Fin second) Bool)

/-- Embed the source and first fresh block into the composite cube. -/
def firstCompositeEmbedding (Source : Type u) (first second : Nat) :
    Sum Source (Fin first) ↪ Sum Source (Fin (first + second)) where
  toFun coordinate :=
    (splitFreshVariableEquiv Source first second).symm (Sum.inl coordinate)
  inj' := by
    intro left right hEqual
    have := (splitFreshVariableEquiv Source first second).symm.injective hEqual
    exact Sum.inl_injective this

/-- Feed the first reduction's designated output into the source coordinates
of the second reduction, while placing its fresh block last. -/
def secondCompositeEmbedding
    {Source : Type u} {Middle : Type v}
    (first second : Nat)
    (designation : Middle ↪ Sum Source (Fin first)) :
    Sum Middle (Fin second) ↪ Sum Source (Fin (first + second)) where
  toFun coordinate :=
    (splitFreshVariableEquiv Source first second).symm
      (match coordinate with
      | Sum.inl middle => Sum.inl (designation middle)
      | Sum.inr fresh => Sum.inr fresh)
  inj' := by
    intro left right hEqual
    have hNested :=
      (splitFreshVariableEquiv Source first second).symm.injective hEqual
    cases left with
    | inl leftMiddle =>
        cases right with
        | inl rightMiddle =>
            exact congrArg Sum.inl (designation.injective (Sum.inl_injective hNested))
        | inr rightFresh => cases hNested
    | inr leftFresh =>
        cases right with
        | inl rightMiddle => cases hNested
        | inr rightFresh =>
            exact congrArg Sum.inr (Sum.inr_injective hNested)

@[simp]
theorem projectAlong_firstCompositeEmbedding
    {Source : Type u} (first second : Nat)
    (assignment : Assignment (Sum Source (Fin (first + second)))) :
    projectAlong (firstCompositeEmbedding Source first second) assignment =
      (splitFreshAssignmentEquiv Source first second assignment).1 := by
  rfl

@[simp]
theorem projectObs_splitFreshAssignment_first
    {Source : Type u} (first second : Nat)
    (assignment : Assignment (Sum Source (Fin (first + second)))) :
    projectObs (splitFreshAssignmentEquiv Source first second assignment).1 =
      projectObs assignment := by
  rfl

/-- Combine a middle assignment and a fresh assignment into the second
reduction's source-plus-fresh cube. -/
def combineSecondAssignment
    {Middle : Type u} {Fresh : Type v}
    (middle : Assignment Middle) (fresh : Assignment Fresh) :
    Assignment (Sum Middle Fresh) :=
  (Equiv.sumArrowEquivProdArrow Middle Fresh Bool).symm (middle, fresh)

@[simp]
theorem combineSecondAssignment_inl
    {Middle : Type u} {Fresh : Type v}
    (middle : Assignment Middle) (fresh : Assignment Fresh)
    (coordinate : Middle) :
    combineSecondAssignment middle fresh (Sum.inl coordinate) =
      middle coordinate :=
  rfl

@[simp]
theorem combineSecondAssignment_inr
    {Middle : Type u} {Fresh : Type v}
    (middle : Assignment Middle) (fresh : Assignment Fresh)
    (coordinate : Fresh) :
    combineSecondAssignment middle fresh (Sum.inr coordinate) =
      fresh coordinate :=
  rfl

@[simp]
theorem projectAlong_secondCompositeEmbedding
    {Source : Type u} {Middle : Type v}
    (first second : Nat)
    (designation : Middle ↪ Sum Source (Fin first))
    (assignment : Assignment (Sum Source (Fin (first + second)))) :
    projectAlong (secondCompositeEmbedding first second designation) assignment =
      combineSecondAssignment
        (projectAlong designation
          (splitFreshAssignmentEquiv Source first second assignment).1)
        (splitFreshAssignmentEquiv Source first second assignment).2 := by
  funext coordinate
  cases coordinate <;> rfl

/-- A coordinate embedding, regarded as a substitution recipe with no fixed
constants. -/
def embeddingRecipe
    {Source : Type u} {Target : Type v}
    (embedding : Source ↪ Target) : Source → CoordinateRecipe Target :=
  fun source => Sum.inl (embedding source)

@[simp]
theorem substituteAssignment_embeddingRecipe
    {Source : Type u} {Target : Type v}
    (embedding : Source ↪ Target) (assignment : Assignment Target) :
    substituteAssignment (embeddingRecipe embedding) assignment =
      projectAlong embedding assignment := by
  rfl

/-- Gibbs factors multiply when nonnegative facial energies and potentials
are added after coordinate substitution. -/
theorem relativeGibbsFactor_add_substitute
    {VarOne : Type u} {VarTwo : Type v} {Target : Type w}
    [Fintype VarOne] [Fintype VarTwo] [Fintype Target]
    [DecidableEq VarOne] [DecidableEq VarTwo] [DecidableEq Target]
    {k : Nat}
    (energyOne potentialOne : FeaturePolynomial VarOne k)
    (energyTwo potentialTwo : FeaturePolynomial VarTwo k)
    (embeddingOne : VarOne ↪ Target)
    (embeddingTwo : VarTwo ↪ Target)
    (hNonnegativeOne : ∀ assignment, 0 ≤ energyOne.eval assignment)
    (hNonnegativeTwo : ∀ assignment, 0 ≤ energyTwo.eval assignment)
    (assignment : Assignment Target) :
    relativeGibbsFactor
        (energyOne.substitute (embeddingRecipe embeddingOne) +
          energyTwo.substitute (embeddingRecipe embeddingTwo))
        (potentialOne.substitute (embeddingRecipe embeddingOne) +
          potentialTwo.substitute (embeddingRecipe embeddingTwo))
        assignment =
      relativeGibbsFactor energyOne potentialOne
          (projectAlong embeddingOne assignment) *
        relativeGibbsFactor energyTwo potentialTwo
          (projectAlong embeddingTwo assignment) := by
  classical
  let assignmentOne := projectAlong embeddingOne assignment
  let assignmentTwo := projectAlong embeddingTwo assignment
  simp only [relativeGibbsFactor, FeaturePolynomial.eval_add,
    FeaturePolynomial.eval_substitute, substituteAssignment_embeddingRecipe]
  change (if energyOne.eval assignmentOne + energyTwo.eval assignmentTwo = 0 then
      ENNReal.ofReal
        (Real.exp (potentialOne.eval assignmentOne +
          potentialTwo.eval assignmentTwo)) else 0) = _
  change (if energyOne.eval assignmentOne + energyTwo.eval assignmentTwo = 0 then
      ENNReal.ofReal
        (Real.exp (potentialOne.eval assignmentOne +
          potentialTwo.eval assignmentTwo)) else 0) =
    (if energyOne.eval assignmentOne = 0 then
        ENNReal.ofReal (Real.exp (potentialOne.eval assignmentOne)) else 0) *
      (if energyTwo.eval assignmentTwo = 0 then
        ENNReal.ofReal (Real.exp (potentialTwo.eval assignmentTwo)) else 0)
  by_cases hOne : energyOne.eval assignmentOne = 0 <;>
    by_cases hTwo : energyTwo.eval assignmentTwo = 0
  · simp [hOne, hTwo, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  · simp [hOne, hTwo]
  · simp [hOne, hTwo]
  · have hSum : energyOne.eval assignmentOne + energyTwo.eval assignmentTwo ≠ 0 := by
      intro hZero
      have hOneNonnegative := hNonnegativeOne assignmentOne
      have hTwoNonnegative := hNonnegativeTwo assignmentTwo
      have : energyOne.eval assignmentOne = 0 := by nlinarith
      exact hOne this
    rw [if_neg hSum]
    simp [hOne, hTwo]

/-- The unnormalized-looking composite weight.  Its total mass is one because
the first extension has middle marginal `D` and the second extension is
normalized relative to `D`. -/
noncomputable def compositeReductionWeight
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second)
    (assignment : Assignment (Sum Source (Fin (first + second)))) : ENNReal :=
  let parts := splitFreshAssignmentEquiv Source first second assignment
  firstReduction.extension parts.1 *
    relativeGibbsFactor secondReduction.relative.energy
      secondReduction.relative.potential
      (combineSecondAssignment
        (projectAlong firstReduction.designation parts.1) parts.2)

/-- The second extension's normalization, written fiberwise over its source
assignment. -/
theorem secondReduction_fiber_sum
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    {k cost : Nat}
    {source : Distribution (Assignment Source)}
    {target : Distribution (Assignment Target)}
    (reduction : GibbsReductionWitness k Source Target source target cost) :
    ∑ sourceAssignment,
        source sourceAssignment *
          (∑ freshAssignment : Assignment (Fin cost),
            relativeGibbsFactor reduction.relative.energy
              reduction.relative.potential
              (combineSecondAssignment sourceAssignment freshAssignment)) = 1 := by
  classical
  let split := Equiv.sumArrowEquivProdArrow Source (Fin cost) Bool
  calc
    ∑ sourceAssignment,
        source sourceAssignment *
          (∑ freshAssignment : Assignment (Fin cost),
            relativeGibbsFactor reduction.relative.energy
              reduction.relative.potential
              (combineSecondAssignment sourceAssignment freshAssignment)) =
        ∑ sourceAssignment, ∑ freshAssignment : Assignment (Fin cost),
          source sourceAssignment *
            relativeGibbsFactor reduction.relative.energy
              reduction.relative.potential
              (combineSecondAssignment sourceAssignment freshAssignment) := by
      apply Finset.sum_congr rfl
      intro sourceAssignment _
      rw [Finset.mul_sum]
    _ = ∑ pair : Assignment Source × Assignment (Fin cost),
          reduction.extension (split.symm pair) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro sourceAssignment _
      apply Finset.sum_congr rfl
      intro freshAssignment _
      rw [reduction.relative.probability_eq]
      rfl
    _ = ∑ assignment, reduction.extension assignment := by
      simpa [split] using split.symm.sum_comp reduction.extension
    _ = 1 := by
      simpa only [tsum_fintype] using reduction.extension.tsum_coe

/-- Composite weights have total mass one. -/
theorem compositeReductionWeight_sum_one
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second) :
    ∑ assignment, compositeReductionWeight firstReduction secondReduction assignment = 1 := by
  classical
  let split := splitFreshAssignmentEquiv Source first second
  let fiberWeight : Assignment Middle → ENNReal := fun middleAssignment =>
    ∑ freshAssignment : Assignment (Fin second),
      relativeGibbsFactor secondReduction.relative.energy
        secondReduction.relative.potential
        (combineSecondAssignment middleAssignment freshAssignment)
  calc
    ∑ assignment, compositeReductionWeight firstReduction secondReduction assignment =
        ∑ pair : Assignment (Sum Source (Fin first)) × Assignment (Fin second),
          firstReduction.extension pair.1 *
            relativeGibbsFactor secondReduction.relative.energy
              secondReduction.relative.potential
              (combineSecondAssignment
                (projectAlong firstReduction.designation pair.1) pair.2) := by
      simpa [compositeReductionWeight, split] using
        split.sum_comp (fun pair =>
          firstReduction.extension pair.1 *
            relativeGibbsFactor secondReduction.relative.energy
              secondReduction.relative.potential
              (combineSecondAssignment
                (projectAlong firstReduction.designation pair.1) pair.2))
    _ = ∑ firstAssignment, firstReduction.extension firstAssignment *
          fiberWeight (projectAlong firstReduction.designation firstAssignment) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro firstAssignment _
      dsimp only [fiberWeight]
      rw [Finset.mul_sum]
    _ = ∑ middleAssignment, middle middleAssignment *
          fiberWeight middleAssignment :=
      sum_probability_mul_of_map firstReduction.extension middle
        (projectAlong firstReduction.designation) firstReduction.marginal fiberWeight
    _ = 1 := secondReduction_fiber_sum secondReduction

/-- The PMF underlying a composite reduction. -/
noncomputable def compositeReductionExtension
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second) :
    Distribution (Assignment (Sum Source (Fin (first + second)))) :=
  PMF.ofFintype (compositeReductionWeight firstReduction secondReduction)
    (compositeReductionWeight_sum_one firstReduction secondReduction)

@[simp]
theorem compositeReductionExtension_apply
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second)
    (assignment : Assignment (Sum Source (Fin (first + second)))) :
    compositeReductionExtension firstReduction secondReduction assignment =
      compositeReductionWeight firstReduction secondReduction assignment :=
  rfl

/-- The exposing energy of a composite reduction. -/
noncomputable def compositeReductionEnergy
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second) :
    FeaturePolynomial (Sum Source (Fin (first + second))) k :=
  firstReduction.relative.energy.substitute
      (embeddingRecipe (firstCompositeEmbedding Source first second)) +
    secondReduction.relative.energy.substitute
      (embeddingRecipe
        (secondCompositeEmbedding first second firstReduction.designation))

/-- The local potential of a composite reduction. -/
noncomputable def compositeReductionPotential
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second) :
    FeaturePolynomial (Sum Source (Fin (first + second))) k :=
  firstReduction.relative.potential.substitute
      (embeddingRecipe (firstCompositeEmbedding Source first second)) +
    secondReduction.relative.potential.substitute
      (embeddingRecipe
        (secondCompositeEmbedding first second firstReduction.designation))

/-- The composite extension has the sum of the two substituted relative Gibbs
certificates. -/
noncomputable def compositeReductionRelativeCertificate
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second) :
    RelativeFaceGibbsCertificate k source
      (compositeReductionExtension firstReduction secondReduction) where
  energy := compositeReductionEnergy firstReduction secondReduction
  energy_nonnegative := by
    intro assignment
    simp only [compositeReductionEnergy, FeaturePolynomial.eval_add,
      FeaturePolynomial.eval_substitute,
      substituteAssignment_embeddingRecipe]
    exact add_nonneg
      (firstReduction.relative.energy_nonnegative _)
      (secondReduction.relative.energy_nonnegative _)
  potential := compositeReductionPotential firstReduction secondReduction
  probability_eq := by
    intro assignment
    rw [compositeReductionExtension_apply]
    unfold compositeReductionWeight
    dsimp only
    rw [firstReduction.relative.probability_eq]
    rw [show projectObs
        (splitFreshAssignmentEquiv Source first second assignment).1 =
          projectObs assignment by
      exact projectObs_splitFreshAssignment_first first second assignment]
    rw [show relativeGibbsFactor
          (compositeReductionEnergy firstReduction secondReduction)
          (compositeReductionPotential firstReduction secondReduction)
          assignment =
        relativeGibbsFactor firstReduction.relative.energy
            firstReduction.relative.potential
            (projectAlong (firstCompositeEmbedding Source first second) assignment) *
          relativeGibbsFactor secondReduction.relative.energy
            secondReduction.relative.potential
            (projectAlong
              (secondCompositeEmbedding first second
                firstReduction.designation) assignment) by
      exact relativeGibbsFactor_add_substitute
        firstReduction.relative.energy firstReduction.relative.potential
        secondReduction.relative.energy secondReduction.relative.potential
        (firstCompositeEmbedding Source first second)
        (secondCompositeEmbedding first second firstReduction.designation)
        firstReduction.relative.energy_nonnegative
        secondReduction.relative.energy_nonnegative assignment]
    rw [projectAlong_firstCompositeEmbedding,
      projectAlong_secondCompositeEmbedding]
    ac_rfl

/-- The composite extension has the second extension as its
source-plus-second-fresh marginal. -/
theorem compositeReductionExtension_map_second
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second) :
    (compositeReductionExtension firstReduction secondReduction).map
        (projectAlong
          (secondCompositeEmbedding first second firstReduction.designation)) =
      secondReduction.extension := by
  classical
  apply PMF.ext
  intro secondAssignment
  rw [PMF.map_apply]
  simp only [tsum_fintype, compositeReductionExtension_apply]
  let splitFirst := splitFreshAssignmentEquiv Source first second
  let splitSecond := Equiv.sumArrowEquivProdArrow Middle (Fin second) Bool
  let secondSource := (splitSecond secondAssignment).1
  let secondFresh := (splitSecond secondAssignment).2
  let factorAtSecond := relativeGibbsFactor
    secondReduction.relative.energy secondReduction.relative.potential
    secondAssignment
  have hReindex :
      (∑ assignment : Assignment (Sum Source (Fin (first + second))),
        if secondAssignment =
            projectAlong
              (secondCompositeEmbedding first second firstReduction.designation)
              assignment then
          compositeReductionWeight firstReduction secondReduction assignment
        else 0) =
      ∑ pair : Assignment (Sum Source (Fin first)) × Assignment (Fin second),
        if secondAssignment =
            combineSecondAssignment
              (projectAlong firstReduction.designation pair.1) pair.2 then
          firstReduction.extension pair.1 *
            relativeGibbsFactor secondReduction.relative.energy
              secondReduction.relative.potential
              (combineSecondAssignment
                (projectAlong firstReduction.designation pair.1) pair.2)
        else 0 := by
    simpa [splitFirst, compositeReductionWeight] using
      splitFirst.sum_comp (fun pair =>
        if secondAssignment =
            combineSecondAssignment
              (projectAlong firstReduction.designation pair.1) pair.2 then
          firstReduction.extension pair.1 *
            relativeGibbsFactor secondReduction.relative.energy
              secondReduction.relative.potential
              (combineSecondAssignment
                (projectAlong firstReduction.designation pair.1) pair.2)
        else 0)
  rw [hReindex, Fintype.sum_prod_type]
  have hInner : ∀ firstAssignment : Assignment (Sum Source (Fin first)),
      (∑ freshAssignment : Assignment (Fin second),
        if secondAssignment =
            combineSecondAssignment
              (projectAlong firstReduction.designation firstAssignment)
              freshAssignment then
          firstReduction.extension firstAssignment *
            relativeGibbsFactor secondReduction.relative.energy
              secondReduction.relative.potential
              (combineSecondAssignment
                (projectAlong firstReduction.designation firstAssignment)
                freshAssignment)
        else 0) =
      if secondSource = projectAlong firstReduction.designation firstAssignment then
        firstReduction.extension firstAssignment * factorAtSecond
      else 0 := by
    intro firstAssignment
    rw [Fintype.sum_eq_single secondFresh]
    · by_cases hSource :
          secondSource = projectAlong firstReduction.designation firstAssignment
      · have hAssignment : secondAssignment =
            combineSecondAssignment
              (projectAlong firstReduction.designation firstAssignment)
              secondFresh := by
          calc
            secondAssignment = splitSecond.symm (splitSecond secondAssignment) :=
              (splitSecond.symm_apply_apply secondAssignment).symm
            _ = splitSecond.symm (secondSource, secondFresh) := rfl
            _ = splitSecond.symm
                (projectAlong firstReduction.designation firstAssignment,
                  secondFresh) := by rw [hSource]
            _ = combineSecondAssignment
                (projectAlong firstReduction.designation firstAssignment)
                secondFresh := by rfl
        simp [hAssignment, hSource, factorAtSecond]
      · have hAssignment : secondAssignment ≠
            combineSecondAssignment
              (projectAlong firstReduction.designation firstAssignment)
              secondFresh := by
          intro hEqual
          have hPair := congrArg splitSecond hEqual
          exact hSource (congrArg Prod.fst hPair)
        simp [hAssignment, hSource]
    · intro freshAssignment hFresh
      have hAssignment : secondAssignment ≠
          combineSecondAssignment
            (projectAlong firstReduction.designation firstAssignment)
            freshAssignment := by
        intro hEqual
        have hPair := congrArg splitSecond hEqual
        have : secondFresh = freshAssignment := congrArg Prod.snd hPair
        exact hFresh this.symm
      simp [hAssignment]
  simp_rw [hInner]
  have hFactor :
      (∑ firstAssignment,
        if secondSource = projectAlong firstReduction.designation firstAssignment then
          firstReduction.extension firstAssignment * factorAtSecond else 0) =
        (∑ firstAssignment,
          if secondSource = projectAlong firstReduction.designation firstAssignment then
            firstReduction.extension firstAssignment else 0) * factorAtSecond := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro firstAssignment _
    by_cases hSource :
        secondSource = projectAlong firstReduction.designation firstAssignment <;>
      simp [hSource]
  rw [hFactor]
  have hMiddleAtSource : middle secondSource =
      ∑ firstAssignment,
        if secondSource = projectAlong firstReduction.designation firstAssignment then
          firstReduction.extension firstAssignment else 0 := by
    have hPoint : middle secondSource =
        ∑' firstAssignment,
          if secondSource =
              projectAlong firstReduction.designation firstAssignment then
            firstReduction.extension firstAssignment else 0 := by
      calc
        middle secondSource =
            (firstReduction.extension.map
              (projectAlong firstReduction.designation)) secondSource := by
          exact congrArg
            (fun distribution : Distribution (Assignment Middle) =>
              distribution secondSource) firstReduction.marginal.symm
        _ = _ := by
          rw [PMF.map_apply]
          apply tsum_congr
          intro firstAssignment
          by_cases hSource : secondSource =
              projectAlong firstReduction.designation firstAssignment <;>
            simp [hSource]
    simp only [tsum_fintype] at hPoint
    exact hPoint
  rw [← hMiddleAtSource, secondReduction.relative.probability_eq]
  rfl

/-- Compose two concrete Gibbs reductions. -/
noncomputable def GibbsReductionWitness.comp
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)}
    (firstReduction :
      GibbsReductionWitness k Source Middle source middle first)
    (secondReduction :
      GibbsReductionWitness k Middle Target middle target second) :
    GibbsReductionWitness k Source Target source target (first + second) where
  extension := compositeReductionExtension firstReduction secondReduction
  relative := compositeReductionRelativeCertificate firstReduction secondReduction
  designation := secondReduction.designation.trans
    (secondCompositeEmbedding first second firstReduction.designation)
  marginal := by
    have hProjection :
        projectAlong
            (secondReduction.designation.trans
              (secondCompositeEmbedding first second firstReduction.designation)) =
          projectAlong secondReduction.designation ∘
            projectAlong
              (secondCompositeEmbedding first second firstReduction.designation) := by
      rfl
    rw [hProjection, ← PMF.map_comp,
      compositeReductionExtension_map_second, secondReduction.marginal]

/-- Composition of exact-cost reduction witnesses. -/
theorem hasGibbsReduction_comp
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k first second : Nat}
    {source : Distribution (Assignment Source)}
    {middle : Distribution (Assignment Middle)}
    {target : Distribution (Assignment Target)} :
    HasGibbsReduction k first Source Middle source middle →
      HasGibbsReduction k second Middle Target middle target →
        HasGibbsReduction k (first + second) Source Target source target := by
  rintro ⟨firstReduction⟩ ⟨secondReduction⟩
  exact ⟨firstReduction.comp secondReduction⟩

/-- Minimum-cost composition, assuming the two displayed minima exist. -/
theorem gibbsReductionCost_comp_le_of_exists
    {Source : Type u} {Middle : Type v} {Target : Type w}
    [Fintype Source] [Fintype Middle] [Fintype Target]
    [DecidableEq Source] [DecidableEq Middle] [DecidableEq Target]
    {k : Nat}
    (source : Distribution (Assignment Source))
    (middle : Distribution (Assignment Middle))
    (target : Distribution (Assignment Target))
    (hFirst : ∃ cost,
      HasGibbsReduction k cost Source Middle source middle)
    (hSecond : ∃ cost,
      HasGibbsReduction k cost Middle Target middle target) :
    gibbsReductionCost k Source Target source target ≤
      gibbsReductionCost k Source Middle source middle +
        gibbsReductionCost k Middle Target middle target := by
  apply gibbsReductionCost_min
  exact hasGibbsReduction_comp
    (gibbsReductionCost_spec k Source Middle source middle hFirst)
    (gibbsReductionCost_spec k Middle Target middle target hSecond)

end KLocality
