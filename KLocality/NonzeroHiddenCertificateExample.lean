import KLocality.MarginalTradeCertificate

namespace KLocality

open scoped BigOperators

/-!
# A full-support exact lower bound at one hidden bit

The visible law has unnormalized weight

`(1 + 1_{x₀x₁x₂ = 111}) (1 + 1_{x₂x₃x₄ = 111})`.

Thus its weights are positive rationals with normalizing constant `41`.  A
degree-six marginal trade vanishes for every quadratic localization with one
hidden bit, including boundary localizations, but evaluates to `6/41^6` on
one side and `7/41^6` on this law.
-/

/-- Interpret a natural number by its five low binary digits. -/
def bitVecFiveOfNat (value : Nat) : BitVec 5 :=
  fun coordinate => value.testBit coordinate

/-- The first boosted cubic upper event. -/
def firstCubicEvent (assignment : BitVec 5) : Bool :=
  assignment 0 && assignment 1 && assignment 2

/-- The second boosted cubic upper event. -/
def secondCubicEvent (assignment : BitVec 5) : Bool :=
  assignment 2 && assignment 3 && assignment 4

/-- Exact rational probability table. -/
def twoCubicWeightsRat (assignment : BitVec 5) : ℚ :=
  ((if firstCubicEvent assignment then 2 else 1) *
    (if secondCubicEvent assignment then 2 else 1)) / 41

theorem twoCubicWeightsRat_pos (assignment : BitVec 5) :
    0 < twoCubicWeightsRat assignment := by
  native_decide +revert

theorem sum_twoCubicWeightsRat :
    (∑ assignment : BitVec 5, twoCubicWeightsRat assignment) = 1 := by
  native_decide

/-- The real table used to construct the PMF. -/
noncomputable def twoCubicWeights (assignment : BitVec 5) : ℝ :=
  twoCubicWeightsRat assignment

/-- Full-support rational target distribution on five visible bits. -/
noncomputable def twoCubicDistribution : Distribution (BitVec 5) :=
  distributionOfRealWeights twoCubicWeights
    (by
      intro assignment
      exact Rat.cast_nonneg.mpr
        (le_of_lt (twoCubicWeightsRat_pos assignment)))
    (by
      have hCast := congrArg (fun value : ℚ => (value : ℝ))
        sum_twoCubicWeightsRat
      simpa [twoCubicWeights, Rat.cast_sum] using hCast)

@[simp]
theorem twoCubicDistribution_apply_toReal (assignment : BitVec 5) :
    (twoCubicDistribution assignment).toReal =
      twoCubicWeights assignment := by
  exact distributionOfRealWeights_apply_toReal _ _ _ assignment

/-- The target really has full support; the lower bound is entirely
weight-sensitive. -/
theorem twoCubicDistribution_support :
    twoCubicDistribution.support = Set.univ := by
  ext assignment
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff twoCubicDistribution assignment).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [twoCubicDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  have hPositive : 0 < twoCubicWeights assignment :=
    Rat.cast_pos.mpr (twoCubicWeightsRat_pos assignment)
  exact (ne_of_gt hPositive) hReal

/-- Six visible configurations, represented by their binary integers. -/
def sexticTuple (a b c d e f : Nat) : Fin 6 → BitVec 5 :=
  ![bitVecFiveOfNat a, bitVecFiveOfNat b, bitVecFiveOfNat c,
    bitVecFiveOfNat d, bitVecFiveOfNat e, bitVecFiveOfNat f]

/-- The three positive monomials in the sextic marginal trade. -/
def oneHiddenSexticPositive : Fin 3 → Fin 6 → BitVec 5 :=
  ![sexticTuple 0 6 9 19 21 28,
    sexticTuple 1 2 12 20 23 25,
    sexticTuple 3 4 8 17 22 29]

/-- The three negative monomials in the sextic marginal trade. -/
def oneHiddenSexticNegative : Fin 3 → Fin 6 → BitVec 5 :=
  ![sexticTuple 0 3 12 21 22 25,
    sexticTuple 1 6 8 19 20 29,
    sexticTuple 2 4 9 17 23 28]

/-- Exact degree-six certificate for one latent bit.  `native_decide` checks
the equality of all 192 expanded joint feature profiles, with multiplicity. -/
def oneHiddenSexticCertificate :
    MarginalTradeCertificate 2 6 3 (Fin 5) (Fin 1) where
  positive := oneHiddenSexticPositive
  negative := oneHiddenSexticNegative
  profileBalance := by native_decide

/-- The same visible trade, specialized to no latent coordinates. -/
def zeroHiddenSexticCertificate :
    MarginalTradeCertificate 2 6 3 (Fin 5) (Fin 0) where
  positive := oneHiddenSexticPositive
  negative := oneHiddenSexticNegative
  profileBalance := by native_decide

def oneHiddenSexticPositiveValueRat : ℚ :=
  ∑ term : Fin 3,
    ∏ index : Fin 6,
      twoCubicWeightsRat (oneHiddenSexticCertificate.positive term index)

def oneHiddenSexticNegativeValueRat : ℚ :=
  ∑ term : Fin 3,
    ∏ index : Fin 6,
      twoCubicWeightsRat (oneHiddenSexticCertificate.negative term index)

theorem oneHiddenSexticPositiveValueRat_eq :
    oneHiddenSexticPositiveValueRat = 6 / (41 : ℚ) ^ 6 := by
  native_decide

theorem oneHiddenSexticNegativeValueRat_eq :
    oneHiddenSexticNegativeValueRat = 7 / (41 : ℚ) ^ 6 := by
  native_decide

theorem oneHiddenSextic_positiveValue :
    oneHiddenSexticCertificate.positiveValue twoCubicWeights =
      6 / (41 : ℝ) ^ 6 := by
  have hCast := congrArg (fun value : ℚ => (value : ℝ))
    oneHiddenSexticPositiveValueRat_eq
  simpa [MarginalTradeCertificate.positiveValue,
    oneHiddenSexticPositiveValueRat, twoCubicWeights,
    Rat.cast_sum, Rat.cast_prod] using hCast

theorem oneHiddenSextic_negativeValue :
    oneHiddenSexticCertificate.negativeValue twoCubicWeights =
      7 / (41 : ℝ) ^ 6 := by
  have hCast := congrArg (fun value : ℚ => (value : ℝ))
    oneHiddenSexticNegativeValueRat_eq
  simpa [MarginalTradeCertificate.negativeValue,
    oneHiddenSexticNegativeValueRat, twoCubicWeights,
    Rat.cast_sum, Rat.cast_prod] using hCast

theorem oneHiddenSextic_detects :
    oneHiddenSexticCertificate.positiveValue
        (fun assignment => (twoCubicDistribution assignment).toReal) ≠
      oneHiddenSexticCertificate.negativeValue
        (fun assignment => (twoCubicDistribution assignment).toReal) := by
  simp_rw [twoCubicDistribution_apply_toReal]
  rw [oneHiddenSextic_positiveValue, oneHiddenSextic_negativeValue]
  norm_num

theorem zeroHiddenSextic_detects :
    zeroHiddenSexticCertificate.positiveValue
        (fun assignment => (twoCubicDistribution assignment).toReal) ≠
      zeroHiddenSexticCertificate.negativeValue
        (fun assignment => (twoCubicDistribution assignment).toReal) := by
  have hPositive : zeroHiddenSexticCertificate.positiveValue twoCubicWeights =
      oneHiddenSexticCertificate.positiveValue twoCubicWeights := rfl
  have hNegative : zeroHiddenSexticCertificate.negativeValue twoCubicWeights =
      oneHiddenSexticCertificate.negativeValue twoCubicWeights := rfl
  simp_rw [twoCubicDistribution_apply_toReal]
  rw [hPositive, hNegative, oneHiddenSextic_positiveValue,
    oneHiddenSextic_negativeValue]
  norm_num

/-- No quadratic localization of the target can use one hidden bit.  Boundary
joint laws are included by the generic certificate theorem. -/
theorem twoCubicDistribution_no_oneHidden :
    ¬HasKLocalizationBits 2 1 5 twoCubicDistribution :=
  oneHiddenSexticCertificate.obstructs_localization oneHiddenSextic_detects

/-- Nor is the target already quadratically local with no hidden bit. -/
theorem twoCubicDistribution_no_zeroHidden :
    ¬HasKLocalizationBits 2 0 5 twoCubicDistribution :=
  zeroHiddenSexticCertificate.obstructs_localization zeroHiddenSextic_detects

/-- The exact certificate family required by the uniform budget theorem for
all latent counts through one. -/
theorem twoCubicTradeCertificates_upTo_one :
    ∀ latentBits, latentBits ≤ 1 →
      ∃ degree termCount,
        ∃ certificate : MarginalTradeCertificate
            2 degree termCount (Fin 5) (Fin latentBits),
          certificate.positiveValue
              (fun assignment => (twoCubicDistribution assignment).toReal) ≠
            certificate.negativeValue
              (fun assignment => (twoCubicDistribution assignment).toReal) := by
  intro latentBits hAtMost
  have hCases : latentBits = 0 ∨ latentBits = 1 := by omega
  rcases hCases with hZero | hOne
  · subst latentBits
    exact ⟨6, 3, zeroHiddenSexticCertificate, zeroHiddenSextic_detects⟩
  · subst latentBits
    exact ⟨6, 3, oneHiddenSexticCertificate, oneHiddenSextic_detects⟩

/-- The first exact boundary-safe full-support lower bound at a nonzero hidden
budget: `LC₂(D) > 1`. -/
theorem twoCubicDistribution_localizationComplexity_gt_one :
    1 < localizationComplexityBits 2 5 twoCubicDistribution :=
  MarginalTradeCertificate.localizationComplexity_gt_of_tradeCertificates
    (by omega : 2 ≤ 2) twoCubicDistribution
      twoCubicTradeCertificates_upTo_one

/-! ## Matching two-hidden construction -/

/-- One violated implication `hidden → visible` contributes one unit of
quadratic energy. -/
def hiddenVisibleViolation
    (joint : Assignment (Sum (Fin 5) (Fin 2)))
    (hidden : Fin 2) (visible : Fin 5) : Nat :=
  if joint (Sum.inr hidden) && !joint (Sum.inl visible) then 1 else 0

/-- Number of failed implications in the two-cubic lift. -/
def twoCubicViolationCount
    (joint : Assignment (Sum (Fin 5) (Fin 2))) : Nat :=
  hiddenVisibleViolation joint 0 0 +
    hiddenVisibleViolation joint 0 1 +
    hiddenVisibleViolation joint 0 2 +
    hiddenVisibleViolation joint 1 2 +
    hiddenVisibleViolation joint 1 3 +
    hiddenVisibleViolation joint 1 4

/-- The 41 valid lifted states.  Hidden bit zero may turn on only above the
first cubic event, and hidden bit one only above the second. -/
def twoCubicLiftedSet :
    Finset (Assignment (Sum (Fin 5) (Fin 2))) :=
  Finset.univ.filter fun joint => twoCubicViolationCount joint = 0

theorem twoCubicLiftedSet_nonempty : twoCubicLiftedSet.Nonempty := by
  native_decide

theorem twoCubicLiftedSet_card : twoCubicLiftedSet.card = 41 := by
  native_decide

/-- One scoped quadratic implication penalty. -/
def hiddenVisiblePenalty (hidden : Fin 2) (visible : Fin 5) :
    LocalEnergyTerm (Sum (Fin 5) (Fin 2)) where
  scope := {Sum.inr hidden, Sum.inl visible}
  value := fun assignment =>
    if assignment ⟨Sum.inr hidden, Finset.mem_insert_self _ _⟩ &&
        !assignment ⟨Sum.inl visible,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ then 1 else 0

@[simp]
theorem hiddenVisiblePenalty_eval
    (hidden : Fin 2) (visible : Fin 5)
    (joint : Assignment (Sum (Fin 5) (Fin 2))) :
    (hiddenVisiblePenalty hidden visible).eval joint =
      if joint (Sum.inr hidden) && !joint (Sum.inl visible) then 1 else 0 :=
  rfl

/-- Six pairwise terms expose the desired lifted support. -/
def twoCubicLiftedTerms :
    List (LocalEnergyTerm (Sum (Fin 5) (Fin 2))) :=
  [hiddenVisiblePenalty 0 0,
    hiddenVisiblePenalty 0 1,
    hiddenVisiblePenalty 0 2,
    hiddenVisiblePenalty 1 2,
    hiddenVisiblePenalty 1 3,
    hiddenVisiblePenalty 1 4]

theorem twoCubicLiftedTerms_respect_two :
    LocalEnergyTermsRespectK 2 twoCubicLiftedTerms := by
  simp [LocalEnergyTermsRespectK, twoCubicLiftedTerms,
    hiddenVisiblePenalty]

theorem localEnergyEval_twoCubicLiftedTerms
    (joint : Assignment (Sum (Fin 5) (Fin 2))) :
    localEnergyEval twoCubicLiftedTerms joint =
      (twoCubicViolationCount joint : ℝ) := by
  simp [localEnergyEval, twoCubicLiftedTerms, twoCubicViolationCount,
    hiddenVisibleViolation]
  ring

theorem twoCubicLiftedTerms_nonnegative
    (joint : Assignment (Sum (Fin 5) (Fin 2))) :
    0 ≤ localEnergyEval twoCubicLiftedTerms joint := by
  rw [localEnergyEval_twoCubicLiftedTerms]
  positivity

theorem twoCubicLiftedSet_is_groundSpace
    (joint : Assignment (Sum (Fin 5) (Fin 2))) :
    joint ∈ twoCubicLiftedSet ↔
      localEnergyEval twoCubicLiftedTerms joint = 0 := by
  rw [localEnergyEval_twoCubicLiftedTerms]
  simp [twoCubicLiftedSet]

/-- Exact rational fiber count underlying the visible marginal calculation. -/
theorem twoCubicLifted_fiber_weight (visible : BitVec 5) :
    (∑ latent : Assignment (Fin 2),
      if jointAssignment visible latent ∈ twoCubicLiftedSet then
        (1 / 41 : ℚ) else 0) = twoCubicWeightsRat visible := by
  native_decide +revert

/-- Projection of the uniform 41-state lifted law is exactly the rational
five-bit target. -/
theorem twoCubicLifted_isMarginalModel :
    IsMarginalModel twoCubicDistribution
      (uniformOn twoCubicLiftedSet twoCubicLiftedSet_nonempty) := by
  classical
  apply PMF.ext
  intro visible
  refine (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      ((uniformOn twoCubicLiftedSet twoCubicLiftedSet_nonempty).map
        projectObs) visible)
    (PMF.apply_ne_top twoCubicDistribution visible)).mp ?_
  rw [map_projectObs_apply_toReal]
  rw [twoCubicDistribution_apply_toReal]
  have hJointWeight : ∀ latent : Assignment (Fin 2),
      ((uniformOn twoCubicLiftedSet twoCubicLiftedSet_nonempty)
        (jointAssignment visible latent)).toReal =
      if jointAssignment visible latent ∈ twoCubicLiftedSet then
        (1 / 41 : ℝ) else 0 := by
    intro latent
    by_cases hMember : jointAssignment visible latent ∈ twoCubicLiftedSet
    · rw [uniformOn_apply_of_mem twoCubicLiftedSet_nonempty hMember,
        twoCubicLiftedSet_card]
      simp [hMember]
    · rw [uniformOn_apply_of_notMem twoCubicLiftedSet_nonempty hMember]
      simp [hMember]
  simp_rw [hJointWeight]
  have hCast := congrArg (fun value : ℚ => (value : ℝ))
    (twoCubicLifted_fiber_weight visible)
  push_cast at hCast
  have hTermCast : ∀ latent : Assignment (Fin 2),
      (((if jointAssignment visible latent ∈ twoCubicLiftedSet then
          (1 / 41 : ℚ) else 0) : ℚ) : ℝ) =
        if jointAssignment visible latent ∈ twoCubicLiftedSet then
          (1 / 41 : ℝ) else 0 := by
    intro latent
    split <;> norm_num
  simp_rw [hTermCast] at hCast
  simpa [twoCubicWeights] using hCast

/-- Two hidden bits suffice: each independently supplies one cubic boost. -/
theorem twoCubicDistribution_has_twoHidden :
    HasKLocalizationBits 2 2 5 twoCubicDistribution :=
  hasKLocalizationBits_of_localEnergyGroundStates
    twoCubicLiftedSet twoCubicLiftedSet_nonempty twoCubicLiftedTerms
    twoCubicLiftedTerms_respect_two twoCubicLiftedTerms_nonnegative
    twoCubicLiftedSet_is_groundSpace twoCubicLifted_isMarginalModel

/-- The target's quadratic localization complexity is exactly two. -/
theorem twoCubicDistribution_localizationComplexity_eq_two :
    localizationComplexityBits 2 5 twoCubicDistribution = 2 := by
  have hUpper := localizationComplexityBits_min
    2 5 twoCubicDistribution 2 twoCubicDistribution_has_twoHidden
  have hLower := twoCubicDistribution_localizationComplexity_gt_one
  omega

end KLocality
