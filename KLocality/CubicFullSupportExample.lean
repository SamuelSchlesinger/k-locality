import KLocality.LogInteractionCertificate
import KLocality.FeatureEmbedding
import KLocality.UniformParityLowerBound
import KLocality.NonzeroHiddenCertificateExample

namespace KLocality

open scoped BigOperators

/-!
# A full-support rational cubic localization lower bound

The distribution in this file assigns probability `2/17` to `1111` and
`1/17` to every other four-bit string.  Its support is the whole cube, but
its log-density has a nonzero four-way interaction, so it is not cubic with
zero hidden bits.

One hidden bit supplies the extra copy of `1111`: the lifted law is uniform
on all states with hidden bit false together with the single all-true state
whose hidden bit is true.  Four pairwise implication penalties expose that
17-state lift.  Consequently the cubic localization complexity is exactly
one.
-/

/-- The all-true point of the four-cube. -/
def allTrueFour : BitVec 4 := fun _ => true

/-- Exact rational probability table, boosted only at `1111`. -/
def boostedFourWeightsRat (assignment : BitVec 4) : ℚ :=
  if assignment = allTrueFour then 2 / 17 else 1 / 17

theorem boostedFourWeightsRat_pos (assignment : BitVec 4) :
    0 < boostedFourWeightsRat assignment := by
  simp only [boostedFourWeightsRat]
  split <;> norm_num

theorem sum_boostedFourWeightsRat :
    (∑ assignment : BitVec 4, boostedFourWeightsRat assignment) = 1 := by
  classical
  calc
    (∑ assignment : BitVec 4, boostedFourWeightsRat assignment) =
        ∑ assignment : BitVec 4,
          ((1 / 17 : ℚ) +
            if assignment = allTrueFour then 1 / 17 else 0) := by
      apply Finset.sum_congr rfl
      intro assignment _
      by_cases hAssignment : assignment = allTrueFour
      · simp [boostedFourWeightsRat, hAssignment]
        norm_num
      · simp [boostedFourWeightsRat, hAssignment]
    _ = (Fintype.card (BitVec 4) : ℚ) * (1 / 17) + 1 / 17 := by
      rw [Finset.sum_add_distrib]
      simp
    _ = 1 := by
      norm_num [BitVec, Fintype.card_fun]

noncomputable def boostedFourWeights (assignment : BitVec 4) : ℝ :=
  boostedFourWeightsRat assignment

/-- The explicit full-support rational target distribution. -/
noncomputable def boostedFourDistribution : Distribution (BitVec 4) :=
  distributionOfRealWeights boostedFourWeights
    (by
      intro assignment
      exact Rat.cast_nonneg.mpr
        (le_of_lt (boostedFourWeightsRat_pos assignment)))
    (by
      have hCast := congrArg (fun value : ℚ => (value : ℝ))
        sum_boostedFourWeightsRat
      simpa [boostedFourWeights, Rat.cast_sum] using hCast)

@[simp]
theorem boostedFourDistribution_apply_toReal (assignment : BitVec 4) :
    (boostedFourDistribution assignment).toReal =
      boostedFourWeights assignment := by
  exact distributionOfRealWeights_apply_toReal _ _ _ assignment

/-- The target has no zero cells, so its lower bound is purely
weight-sensitive. -/
theorem boostedFourDistribution_support :
    boostedFourDistribution.support = Set.univ := by
  ext assignment
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff boostedFourDistribution assignment).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [boostedFourDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  have hPositive : 0 < boostedFourWeights assignment :=
    Rat.cast_pos.mpr (boostedFourWeightsRat_pos assignment)
  exact (ne_of_gt hPositive) hReal

/-- Alternating direction on the four-cube. -/
def cubicDirectionRat (assignment : BitVec 4) : ℚ :=
  evenParityDirectionRat 4 assignment

/-- The alternating four-cube direction annihilates every cubic monomial. -/
theorem cubicDirectionRat_momentBalance :
    ∀ scope : FeatureScope (Fin 4) 3,
      ∑ assignment : BitVec 4,
        cubicDirectionRat assignment *
          rationalMonomialValue scope.1 assignment = 0 := by
  intro scope
  simpa [cubicDirectionRat] using
    (sum_evenParityDirectionRat_mul_rationalMonomialValue_eq_zero
      scope (by omega))

theorem sum_cubicDirectionRat :
    (∑ assignment : BitVec 4, cubicDirectionRat assignment) = 0 := by
  let empty : FeatureScope (Fin 4) 3 := ⟨∅, by simp⟩
  have hBalance := cubicDirectionRat_momentBalance empty
  simpa [rationalMonomialValue] using hBalance

theorem cubicDirectionRat_allTrueFour :
    cubicDirectionRat allTrueFour = -1 := by
  norm_num [cubicDirectionRat, evenParityDirectionRat, allTrueFour,
    parityCoordinateSign, Fin.prod_univ_succ]

theorem boostedFour_log_formula (assignment : BitVec 4) :
    Real.log (boostedFourWeights assignment) =
      Real.log (1 / 17 : ℝ) +
        if assignment = allTrueFour then
          Real.log (2 / 17 : ℝ) - Real.log (1 / 17 : ℝ)
        else 0 := by
  by_cases hAssignment : assignment = allTrueFour
  · simp [boostedFourWeights, boostedFourWeightsRat, hAssignment]
  · simp [boostedFourWeights, boostedFourWeightsRat, hAssignment]

/-- The alternating functional detects the four-way log interaction. -/
theorem boostedFour_alternating_log_sum :
    (∑ assignment : BitVec 4,
      (cubicDirectionRat assignment : ℝ) *
        Real.log (boostedFourWeights assignment)) =
      Real.log (1 / 17 : ℝ) - Real.log (2 / 17 : ℝ) := by
  classical
  simp_rw [boostedFour_log_formula, mul_add]
  rw [Finset.sum_add_distrib]
  have hCast := congrArg (fun value : ℚ => (value : ℝ))
    sum_cubicDirectionRat
  have hDirectionSum :
      (∑ assignment : BitVec 4,
        (cubicDirectionRat assignment : ℝ)) = 0 := by
    simpa [Rat.cast_sum] using hCast
  have hConstant :
      (∑ assignment : BitVec 4,
        (cubicDirectionRat assignment : ℝ) *
          Real.log (1 / 17 : ℝ)) = 0 := by
    calc
      _ = Real.log (1 / 17 : ℝ) *
          ∑ assignment : BitVec 4,
            (cubicDirectionRat assignment : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro assignment _
        ring
      _ = 0 := by rw [hDirectionSum, mul_zero]
  rw [hConstant, zero_add]
  simp [cubicDirectionRat_allTrueFour]
  ring

/-- Rational log-interaction certificate for the target. -/
noncomputable def boostedFourLogInteractionCertificate :
    RationalLogInteractionCertificate 3 boostedFourDistribution where
  direction := cubicDirectionRat
  momentBalance := cubicDirectionRat_momentBalance
  detectsLogDensity := by
    intro hZero
    have hTable :
        (∑ assignment : BitVec 4,
          (cubicDirectionRat assignment : ℝ) *
            Real.log (boostedFourDistribution assignment).toReal) =
          Real.log (1 / 17 : ℝ) - Real.log (2 / 17 : ℝ) := by
      calc
        _ = ∑ assignment : BitVec 4,
            (cubicDirectionRat assignment : ℝ) *
              Real.log (boostedFourWeights assignment) := by
          apply Finset.sum_congr rfl
          intro assignment _
          rw [boostedFourDistribution_apply_toReal]
        _ = _ := boostedFour_alternating_log_sum
    rw [hTable] at hZero
    have hLogNe : Real.log (1 / 17 : ℝ) ≠ Real.log (2 / 17 : ℝ) := by
      intro hEqual
      have hNumbers : (1 / 17 : ℝ) = 2 / 17 :=
        Real.log_injOn_pos (by norm_num) (by norm_num) hEqual
      norm_num at hNumbers
    exact hLogNe (sub_eq_zero.mp hZero)

/-- The full-support rational target is not already cubic. -/
theorem boostedFourDistribution_not_threeLocal :
    ¬IsKLocalMarginal 3 boostedFourDistribution :=
  boostedFourLogInteractionCertificate.not_isKLocalMarginal
    boostedFourDistribution_support

/-- Every cubic localization of the target needs a hidden bit. -/
theorem boostedFourDistribution_localizationComplexity_pos :
    0 < localizationComplexityBits 3 4 boostedFourDistribution :=
  boostedFourLogInteractionCertificate.localizationComplexity_pos
    (by omega) boostedFourDistribution_support

/-! ## Matching one-hidden construction -/

/-- One failed implication from the hidden bit to a visible coordinate. -/
def boostedFourViolation
    (joint : Assignment (Sum (Fin 4) (Fin 1)))
    (visible : Fin 4) : Nat :=
  if joint (Sum.inr 0) && !joint (Sum.inl visible) then 1 else 0

def boostedFourViolationCount
    (joint : Assignment (Sum (Fin 4) (Fin 1))) : Nat :=
  boostedFourViolation joint 0 + boostedFourViolation joint 1 +
    boostedFourViolation joint 2 + boostedFourViolation joint 3

/-- All 16 states with hidden bit false, plus the all-true state with hidden
bit true. -/
def boostedFourLiftedSet :
    Finset (Assignment (Sum (Fin 4) (Fin 1))) :=
  Finset.univ.filter fun joint => boostedFourViolationCount joint = 0

theorem boostedFourLiftedSet_nonempty : boostedFourLiftedSet.Nonempty := by
  decide

theorem boostedFourLiftedSet_card : boostedFourLiftedSet.card = 17 := by
  decide

def boostedFourPenalty (visible : Fin 4) :
    LocalEnergyTerm (Sum (Fin 4) (Fin 1)) where
  scope := {Sum.inr 0, Sum.inl visible}
  value := fun assignment =>
    if assignment ⟨Sum.inr 0, Finset.mem_insert_self _ _⟩ &&
        !assignment ⟨Sum.inl visible,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ then 1 else 0

@[simp]
theorem boostedFourPenalty_eval
    (visible : Fin 4)
    (joint : Assignment (Sum (Fin 4) (Fin 1))) :
    (boostedFourPenalty visible).eval joint =
      if joint (Sum.inr 0) && !joint (Sum.inl visible) then 1 else 0 :=
  rfl

def boostedFourLiftedTerms :
    List (LocalEnergyTerm (Sum (Fin 4) (Fin 1))) :=
  [boostedFourPenalty 0, boostedFourPenalty 1,
    boostedFourPenalty 2, boostedFourPenalty 3]

theorem boostedFourLiftedTerms_respect_two :
    LocalEnergyTermsRespectK 2 boostedFourLiftedTerms := by
  simp [LocalEnergyTermsRespectK, boostedFourLiftedTerms,
    boostedFourPenalty]

theorem localEnergyEval_boostedFourLiftedTerms
    (joint : Assignment (Sum (Fin 4) (Fin 1))) :
    localEnergyEval boostedFourLiftedTerms joint =
      (boostedFourViolationCount joint : ℝ) := by
  simp [localEnergyEval, boostedFourLiftedTerms,
    boostedFourViolationCount, boostedFourViolation]
  ring

theorem boostedFourLiftedTerms_nonnegative
    (joint : Assignment (Sum (Fin 4) (Fin 1))) :
    0 ≤ localEnergyEval boostedFourLiftedTerms joint := by
  rw [localEnergyEval_boostedFourLiftedTerms]
  positivity

theorem boostedFourLiftedSet_is_groundSpace
    (joint : Assignment (Sum (Fin 4) (Fin 1))) :
    joint ∈ boostedFourLiftedSet ↔
      localEnergyEval boostedFourLiftedTerms joint = 0 := by
  rw [localEnergyEval_boostedFourLiftedTerms]
  simp [boostedFourLiftedSet]

theorem boostedFourLifted_fiber_card (visible : BitVec 4) :
    ((Finset.univ : Finset (Assignment (Fin 1))).filter fun latent =>
      jointAssignment visible latent ∈ boostedFourLiftedSet).card =
        if visible = allTrueFour then 2 else 1 := by
  decide +revert

theorem boostedFourLifted_fiber_weight (visible : BitVec 4) :
    (∑ latent : Assignment (Fin 1),
      if jointAssignment visible latent ∈ boostedFourLiftedSet then
        (1 / 17 : ℚ) else 0) = boostedFourWeightsRat visible := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [boostedFourLifted_fiber_card]
  by_cases hVisible : visible = allTrueFour
  · simp [boostedFourWeightsRat, hVisible]
    norm_num
  · simp [boostedFourWeightsRat, hVisible]

theorem boostedFourLifted_isMarginalModel :
    IsMarginalModel boostedFourDistribution
      (uniformOn boostedFourLiftedSet boostedFourLiftedSet_nonempty) := by
  classical
  apply PMF.ext
  intro visible
  refine (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      ((uniformOn boostedFourLiftedSet boostedFourLiftedSet_nonempty).map
        projectObs) visible)
    (PMF.apply_ne_top boostedFourDistribution visible)).mp ?_
  rw [map_projectObs_apply_toReal]
  rw [boostedFourDistribution_apply_toReal]
  have hJointWeight : ∀ latent : Assignment (Fin 1),
      ((uniformOn boostedFourLiftedSet boostedFourLiftedSet_nonempty)
        (jointAssignment visible latent)).toReal =
      if jointAssignment visible latent ∈ boostedFourLiftedSet then
        (1 / 17 : ℝ) else 0 := by
    intro latent
    by_cases hMember : jointAssignment visible latent ∈ boostedFourLiftedSet
    · rw [uniformOn_apply_of_mem boostedFourLiftedSet_nonempty hMember,
        boostedFourLiftedSet_card]
      simp [hMember]
    · rw [uniformOn_apply_of_notMem boostedFourLiftedSet_nonempty hMember]
      simp [hMember]
  simp_rw [hJointWeight]
  have hCast := congrArg (fun value : ℚ => (value : ℝ))
    (boostedFourLifted_fiber_weight visible)
  push_cast at hCast
  have hTermCast : ∀ latent : Assignment (Fin 1),
      (((if jointAssignment visible latent ∈ boostedFourLiftedSet then
          (1 / 17 : ℚ) else 0) : ℚ) : ℝ) =
        if jointAssignment visible latent ∈ boostedFourLiftedSet then
          (1 / 17 : ℝ) else 0 := by
    intro latent
    split <;> norm_num
  simp_rw [hTermCast] at hCast
  simpa [boostedFourWeights] using hCast

theorem boostedFourDistribution_has_oneHidden_quadratic :
    HasKLocalizationBits 2 1 4 boostedFourDistribution :=
  hasKLocalizationBits_of_localEnergyGroundStates
    boostedFourLiftedSet boostedFourLiftedSet_nonempty
    boostedFourLiftedTerms boostedFourLiftedTerms_respect_two
    boostedFourLiftedTerms_nonnegative boostedFourLiftedSet_is_groundSpace
    boostedFourLifted_isMarginalModel

theorem boostedFourDistribution_has_oneHidden :
    HasKLocalizationBits 3 1 4 boostedFourDistribution :=
  hasKLocalizationBits_mono (by omega)
    boostedFourDistribution_has_oneHidden_quadratic

/-- Exact full-support cubic localization complexity. -/
theorem boostedFourDistribution_localizationComplexity_eq_one :
    localizationComplexityBits 3 4 boostedFourDistribution = 1 := by
  have hUpper := localizationComplexityBits_min
    3 4 boostedFourDistribution 1 boostedFourDistribution_has_oneHidden
  have hLower := boostedFourDistribution_localizationComplexity_pos
  omega

/-! ## Adjacent-locality comparison -/

/-- The full four-coordinate scope, admissible at locality four. -/
def fullScopeFour : FeatureScope (Fin 4) 4 :=
  ⟨Finset.univ, by simp⟩

theorem monomialValue_fullScopeFour (assignment : BitVec 4) :
    monomialValue fullScopeFour.1 assignment =
      if assignment = allTrueFour then 1 else 0 := by
  classical
  change monomialValue (Finset.univ : Finset (Fin 4)) assignment = _
  have hSubset :
      (Finset.univ : Finset (Fin 4)) ⊆ trueCoordinates assignment ↔
        assignment = allTrueFour := by
    constructor
    · intro hAll
      funext coordinate
      exact (mem_trueCoordinates assignment coordinate).1
        (hAll (Finset.mem_univ coordinate))
    · rintro rfl
      intro coordinate _
      simp [mem_trueCoordinates, allTrueFour]
  unfold monomialValue
  by_cases hAssignment : assignment = allTrueFour
  · have hCondition :
        (Finset.univ : Finset (Fin 4)) ⊆
          trueCoordinates assignment := hSubset.2 hAssignment
    rw [if_pos hCondition, if_pos hAssignment]
  · have hNotSubset :
        ¬(Finset.univ : Finset (Fin 4)) ⊆
          trueCoordinates assignment := by
      exact fun h => hAssignment (hSubset.1 h)
    rw [if_neg hNotSubset, if_neg hAssignment]

/-- A quartic log-density for the boosted point law. -/
noncomputable def boostedFourQuarticLogPolynomial :
    FeaturePolynomial (Fin 4) 4 :=
  FeaturePolynomial.constant 4 (Real.log (1 / 17 : ℝ)) +
    FeaturePolynomial.single fullScopeFour
      (Real.log (2 / 17 : ℝ) - Real.log (1 / 17 : ℝ))

@[simp]
theorem boostedFourQuarticLogPolynomial_eval (assignment : BitVec 4) :
    boostedFourQuarticLogPolynomial.eval assignment =
      Real.log (boostedFourWeights assignment) := by
  rw [boostedFourQuarticLogPolynomial, FeaturePolynomial.eval_add,
    FeaturePolynomial.eval_constant, FeaturePolynomial.eval_single,
    monomialValue_fullScopeFour, boostedFour_log_formula]
  by_cases hAssignment : assignment = allTrueFour <;>
    simp [hAssignment]

/-- Raising locality by one removes the only obstruction: the target itself
is a zero-hidden quartic Gibbs law. -/
theorem boostedFourDistribution_is_fourLocal :
    IsKLocalMarginal 4 boostedFourDistribution := by
  apply (isKLocalMarginal_iff_fullSupport_logDensity
    4 boostedFourDistribution boostedFourDistribution_support).2
  exact ⟨boostedFourQuarticLogPolynomial, fun assignment => by
    rw [boostedFourDistribution_apply_toReal]
    exact (boostedFourQuarticLogPolynomial_eval assignment).symm⟩

theorem boostedFourDistribution_localizationComplexity_four_eq_zero :
    localizationComplexityBits 4 4 boostedFourDistribution = 0 := by
  exact (localizationComplexity_eq_zero_iff_isKLocalMarginal
    (by omega) boostedFourDistribution).2
      boostedFourDistribution_is_fourLocal

end KLocality
