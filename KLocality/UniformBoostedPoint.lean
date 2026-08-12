import KLocality.LogInteractionCertificate
import KLocality.FeatureEmbedding
import KLocality.UniformParityLowerBound
import KLocality.MarginalTradeCertificate

namespace KLocality

open scoped BigOperators

/-!
# Uniform full-support boosted-point lower bounds

For every cube dimension `n`, boost only the all-true point: give it rational
weight `2 / (2^n + 1)` and every other point weight `1 / (2^n + 1)`.
The resulting law has full support.  Whenever `k < n`, its log-density has a
nonzero `n`-way alternating interaction, so it cannot be `k`-local without a
hidden bit.

The second half of this file constructs one pairwise hidden bit realizing the
boost.  Thus the family has exact localization complexity one throughout the
range `2 <= k < n`, while it becomes zero-hidden at locality `n`.
-/

/-- The all-true point of an arbitrary Boolean cube. -/
def allTrueBitVec (n : Nat) : BitVec n := fun _ => true

/-- Rational base weight of the boosted-point law. -/
def boostedPointBaseWeightRat (n : Nat) : ℚ :=
  1 / ((2 : ℚ) ^ n + 1)

/-- Rational doubled weight at the distinguished point. -/
def boostedPointDoubleWeightRat (n : Nat) : ℚ :=
  2 / ((2 : ℚ) ^ n + 1)

/-- Exact rational table with a single doubled cell. -/
def boostedPointWeightsRat (n : Nat) (assignment : BitVec n) : ℚ :=
  if assignment = allTrueBitVec n then
    boostedPointDoubleWeightRat n
  else boostedPointBaseWeightRat n

theorem boostedPointBaseWeightRat_pos (n : Nat) :
    0 < boostedPointBaseWeightRat n := by
  unfold boostedPointBaseWeightRat
  positivity

theorem boostedPointDoubleWeightRat_pos (n : Nat) :
    0 < boostedPointDoubleWeightRat n := by
  unfold boostedPointDoubleWeightRat
  positivity

theorem boostedPointWeightsRat_pos (n : Nat) (assignment : BitVec n) :
    0 < boostedPointWeightsRat n assignment := by
  simp only [boostedPointWeightsRat]
  split
  · exact boostedPointDoubleWeightRat_pos n
  · exact boostedPointBaseWeightRat_pos n

theorem sum_boostedPointWeightsRat (n : Nat) :
    (∑ assignment : BitVec n, boostedPointWeightsRat n assignment) = 1 := by
  classical
  calc
    (∑ assignment : BitVec n, boostedPointWeightsRat n assignment) =
        ∑ assignment : BitVec n,
          (boostedPointBaseWeightRat n +
            if assignment = allTrueBitVec n then
              boostedPointBaseWeightRat n else 0) := by
      apply Finset.sum_congr rfl
      intro assignment _
      by_cases hAssignment : assignment = allTrueBitVec n
      · simp [boostedPointWeightsRat, boostedPointBaseWeightRat,
          boostedPointDoubleWeightRat, hAssignment]
        ring
      · simp [boostedPointWeightsRat, hAssignment]
    _ = (Fintype.card (BitVec n) : ℚ) *
          boostedPointBaseWeightRat n + boostedPointBaseWeightRat n := by
      rw [Finset.sum_add_distrib]
      simp
    _ = 1 := by
      simp only [BitVec, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin,
        Nat.cast_pow, Nat.cast_ofNat, boostedPointBaseWeightRat]
      have hDenominator : ((2 : ℚ) ^ n + 1) ≠ 0 := by positivity
      field_simp

/-- Real presentation of the rational table. -/
noncomputable def boostedPointWeights
    (n : Nat) (assignment : BitVec n) : ℝ :=
  boostedPointWeightsRat n assignment

/-- Natural-number-parameterized full-support rational distribution. -/
noncomputable def boostedPointDistribution (n : Nat) :
    Distribution (BitVec n) :=
  distributionOfRealWeights (boostedPointWeights n)
    (by
      intro assignment
      exact Rat.cast_nonneg.mpr
        (le_of_lt (boostedPointWeightsRat_pos n assignment)))
    (by
      have hCast := congrArg (fun value : ℚ => (value : ℝ))
        (sum_boostedPointWeightsRat n)
      simpa [boostedPointWeights, Rat.cast_sum] using hCast)

@[simp]
theorem boostedPointDistribution_apply_toReal
    (n : Nat) (assignment : BitVec n) :
    (boostedPointDistribution n assignment).toReal =
      boostedPointWeights n assignment := by
  exact distributionOfRealWeights_apply_toReal _ _ _ assignment

/-- Every cell is positive. -/
theorem boostedPointDistribution_support (n : Nat) :
    (boostedPointDistribution n).support = Set.univ := by
  ext assignment
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff (boostedPointDistribution n) assignment).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [boostedPointDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  have hPositive : 0 < boostedPointWeights n assignment :=
    Rat.cast_pos.mpr (boostedPointWeightsRat_pos n assignment)
  exact (ne_of_gt hPositive) hReal

/-! ## Uniform log-interaction obstruction -/

/-- Pointwise logarithm decomposition into a constant and one all-true
indicator. -/
theorem boostedPoint_log_formula (n : Nat) (assignment : BitVec n) :
    Real.log (boostedPointWeights n assignment) =
      Real.log (boostedPointBaseWeightRat n : ℝ) +
        if assignment = allTrueBitVec n then
          Real.log (boostedPointDoubleWeightRat n : ℝ) -
            Real.log (boostedPointBaseWeightRat n : ℝ)
        else 0 := by
  by_cases hAssignment : assignment = allTrueBitVec n
  · simp [boostedPointWeights, boostedPointWeightsRat, hAssignment]
  · simp [boostedPointWeights, boostedPointWeightsRat, hAssignment]

/-- Pairing the log table with the alternating cube character isolates the
single boosted cell. -/
theorem boostedPoint_alternating_log_sum
    {n : Nat} (hn : 0 < n) :
    (∑ assignment : BitVec n,
      (evenParityDirectionRat n assignment : ℝ) *
        Real.log (boostedPointWeights n assignment)) =
      (evenParityDirectionRat n (allTrueBitVec n) : ℝ) *
        (Real.log (boostedPointDoubleWeightRat n : ℝ) -
          Real.log (boostedPointBaseWeightRat n : ℝ)) := by
  classical
  simp_rw [boostedPoint_log_formula, mul_add]
  rw [Finset.sum_add_distrib]
  have hCast := congrArg (fun value : ℚ => (value : ℝ))
    (sum_evenParityDirectionRat_eq_zero hn)
  have hDirectionSum :
      (∑ assignment : BitVec n,
        (evenParityDirectionRat n assignment : ℝ)) = 0 := by
    simpa [Rat.cast_sum] using hCast
  have hConstant :
      (∑ assignment : BitVec n,
        (evenParityDirectionRat n assignment : ℝ) *
          Real.log (boostedPointBaseWeightRat n : ℝ)) = 0 := by
    calc
      _ = Real.log (boostedPointBaseWeightRat n : ℝ) *
          ∑ assignment : BitVec n,
            (evenParityDirectionRat n assignment : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro assignment _
        ring
      _ = 0 := by rw [hDirectionSum, mul_zero]
  rw [hConstant, zero_add]
  simp

theorem boostedPoint_log_gap_ne_zero (n : Nat) :
    Real.log (boostedPointDoubleWeightRat n : ℝ) -
        Real.log (boostedPointBaseWeightRat n : ℝ) ≠ 0 := by
  have hBasePos : 0 < (boostedPointBaseWeightRat n : ℝ) :=
    Rat.cast_pos.mpr (boostedPointBaseWeightRat_pos n)
  have hDoublePos : 0 < (boostedPointDoubleWeightRat n : ℝ) :=
    Rat.cast_pos.mpr (boostedPointDoubleWeightRat_pos n)
  have hWeightLtRat :
      boostedPointBaseWeightRat n < boostedPointDoubleWeightRat n := by
    unfold boostedPointBaseWeightRat boostedPointDoubleWeightRat
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hWeightLt :
      (boostedPointBaseWeightRat n : ℝ) <
        (boostedPointDoubleWeightRat n : ℝ) :=
    Rat.cast_lt.mpr hWeightLtRat
  intro hZero
  have hLogEq :
      Real.log (boostedPointDoubleWeightRat n : ℝ) =
        Real.log (boostedPointBaseWeightRat n : ℝ) :=
    sub_eq_zero.mp hZero
  have hWeightsEq :
      (boostedPointDoubleWeightRat n : ℝ) =
        (boostedPointBaseWeightRat n : ℝ) :=
    Real.log_injOn_pos hDoublePos hBasePos hLogEq
  exact (ne_of_gt hWeightLt) hWeightsEq

/-- Uniform rational log-interaction certificate below the full cube degree. -/
noncomputable def boostedPointLogInteractionCertificate
    {k n : Nat} (hSize : k < n) :
    RationalLogInteractionCertificate k (boostedPointDistribution n) where
  direction := evenParityDirectionRat n
  momentBalance := fun scope =>
    sum_evenParityDirectionRat_mul_rationalMonomialValue_eq_zero
      scope hSize
  detectsLogDensity := by
    intro hZero
    have hn : 0 < n := by omega
    have hTable :
        (∑ assignment : BitVec n,
          (evenParityDirectionRat n assignment : ℝ) *
            Real.log (boostedPointDistribution n assignment).toReal) =
          (evenParityDirectionRat n (allTrueBitVec n) : ℝ) *
            (Real.log (boostedPointDoubleWeightRat n : ℝ) -
              Real.log (boostedPointBaseWeightRat n : ℝ)) := by
      calc
        _ = ∑ assignment : BitVec n,
            (evenParityDirectionRat n assignment : ℝ) *
              Real.log (boostedPointWeights n assignment) := by
          apply Finset.sum_congr rfl
          intro assignment _
          rw [boostedPointDistribution_apply_toReal]
        _ = _ := boostedPoint_alternating_log_sum hn
    rw [hTable] at hZero
    exact (mul_ne_zero
      (Rat.cast_ne_zero.mpr
        (evenParityDirectionRat_ne_zero n (allTrueBitVec n)))
      (boostedPoint_log_gap_ne_zero n)) hZero

/-- Every locality order strictly below `n` needs at least one hidden bit. -/
theorem boostedPoint_localizationComplexity_pos
    {k n : Nat} (hk : 2 ≤ k) (hSize : k < n) :
    0 < localizationComplexityBits k n (boostedPointDistribution n) :=
  (boostedPointLogInteractionCertificate hSize).localizationComplexity_pos
    hk (boostedPointDistribution_support n)

/-! ## Uniform one-hidden lift -/

/-- The lifted support contains every state with hidden bit false and, with
hidden bit true, only the all-true visible point. -/
def boostedPointLiftedSet (n : Nat) :
    Finset (Assignment (Sum (Fin n) (Fin 1))) :=
  Finset.univ.filter fun joint =>
    joint (Sum.inr 0) = false ∨
      projectObs joint = allTrueBitVec n

@[simp]
theorem jointAssignment_mem_boostedPointLiftedSet
    (n : Nat) (visible : BitVec n) (latent : Assignment (Fin 1)) :
    jointAssignment visible latent ∈ boostedPointLiftedSet n ↔
      latent 0 = false ∨ visible = allTrueBitVec n := by
  simp [boostedPointLiftedSet]

theorem boostedPointLiftedSet_nonempty (n : Nat) :
    (boostedPointLiftedSet n).Nonempty := by
  refine ⟨jointAssignment (allTrueBitVec n) (allFalseBitVec 1), ?_⟩
  simp

/-- Exactly one hidden witness lies above an ordinary visible point and two
lie above the boosted point. -/
theorem boostedPointLifted_fiber_card (n : Nat) (visible : BitVec n) :
    ((Finset.univ : Finset (Assignment (Fin 1))).filter fun latent =>
      jointAssignment visible latent ∈ boostedPointLiftedSet n).card =
        if visible = allTrueBitVec n then 2 else 1 := by
  classical
  by_cases hVisible : visible = allTrueBitVec n
  · subst visible
    simp [Fintype.card_bool]
  · have hFilter :
        ((Finset.univ : Finset (Assignment (Fin 1))).filter fun latent =>
          jointAssignment visible latent ∈ boostedPointLiftedSet n) =
            {allFalseBitVec 1} := by
      ext latent
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [jointAssignment_mem_boostedPointLiftedSet]
      simp only [hVisible, or_false]
      constructor
      · intro hFalse
        funext coordinate
        fin_cases coordinate
        exact hFalse
      · rintro rfl
        rfl
    rw [hFilter]
    simp [hVisible]

/-- The total lifted support has `2^n + 1` states. -/
theorem boostedPointLiftedSet_card (n : Nat) :
    (boostedPointLiftedSet n).card = 2 ^ n + 1 := by
  classical
  calc
    (boostedPointLiftedSet n).card =
        ∑ joint : Assignment (Sum (Fin n) (Fin 1)),
          if joint ∈ boostedPointLiftedSet n then 1 else 0 := by
      simp
    _ = ∑ visible : BitVec n,
          ∑ latent : Assignment (Fin 1),
            if jointAssignment visible latent ∈ boostedPointLiftedSet n then
              1 else 0 := by
      rw [← (jointAssignmentEquiv (Fin n) (Fin 1)).symm.sum_comp]
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ visible : BitVec n,
          if visible = allTrueBitVec n then 2 else 1 := by
      apply Finset.sum_congr rfl
      intro visible _
      rw [← boostedPointLifted_fiber_card n visible]
      simp
    _ = ∑ visible : BitVec n,
          (1 + if visible = allTrueBitVec n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro visible _
      split <;> rfl
    _ = 2 ^ n + 1 := by
      rw [Finset.sum_add_distrib]
      simp [BitVec, Fintype.card_fin,
        Fintype.card_bool]

/-- Exact rational contribution of a hidden fiber. -/
theorem boostedPointLifted_fiber_weight (n : Nat) (visible : BitVec n) :
    (∑ latent : Assignment (Fin 1),
      if jointAssignment visible latent ∈ boostedPointLiftedSet n then
        boostedPointBaseWeightRat n else 0) =
      boostedPointWeightsRat n visible := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [boostedPointLifted_fiber_card]
  by_cases hVisible : visible = allTrueBitVec n
  · simp [boostedPointWeightsRat, boostedPointDoubleWeightRat,
      boostedPointBaseWeightRat, hVisible]
    ring
  · simp [boostedPointWeightsRat, hVisible]

/-- One failed implication from the hidden bit to a visible coordinate. -/
def boostedPointViolation
    {n : Nat} (joint : Assignment (Sum (Fin n) (Fin 1)))
    (visible : Fin n) : Nat :=
  if joint (Sum.inr 0) && !joint (Sum.inl visible) then 1 else 0

/-- Total number of failed hidden-to-visible implications. -/
def boostedPointViolationCount
    {n : Nat} (joint : Assignment (Sum (Fin n) (Fin 1))) : Nat :=
  ∑ visible : Fin n, boostedPointViolation joint visible

theorem boostedPointViolationCount_eq_zero_iff
    {n : Nat} (joint : Assignment (Sum (Fin n) (Fin 1))) :
    boostedPointViolationCount joint = 0 ↔
      joint (Sum.inr 0) = false ∨
        projectObs joint = allTrueBitVec n := by
  classical
  constructor
  · intro hZero
    by_cases hHidden : joint (Sum.inr 0) = false
    · exact Or.inl hHidden
    · right
      have hHiddenTrue : joint (Sum.inr 0) = true :=
        Bool.eq_true_of_not_eq_false hHidden
      funext coordinate
      change joint (Sum.inl coordinate) = true
      cases hVisible : joint (Sum.inl coordinate) with
      | false =>
          have hTerm : boostedPointViolation joint coordinate = 1 := by
            simp [boostedPointViolation, hHiddenTrue, hVisible]
          have hLe : boostedPointViolation joint coordinate ≤
              boostedPointViolationCount joint := by
            unfold boostedPointViolationCount
            exact Finset.single_le_sum
              (fun candidate _ => Nat.zero_le
                (boostedPointViolation joint candidate))
              (Finset.mem_univ coordinate)
          rw [hTerm, hZero] at hLe
          omega
      | true => rfl
  · rintro (hHidden | hVisible)
    · unfold boostedPointViolationCount boostedPointViolation
      apply Finset.sum_eq_zero
      intro visible _
      simp [hHidden]
    · unfold boostedPointViolationCount
      apply Finset.sum_eq_zero
      intro visible _
      have hTrue : joint (Sum.inl visible) = true := by
        have hAt := congrFun hVisible visible
        simpa [projectObs, allTrueBitVec] using hAt
      simp [boostedPointViolation, hTrue]

/-- A scoped pairwise implication penalty. -/
def boostedPointPenalty {n : Nat} (visible : Fin n) :
    LocalEnergyTerm (Sum (Fin n) (Fin 1)) where
  scope := {Sum.inr 0, Sum.inl visible}
  value := fun assignment =>
    if assignment ⟨Sum.inr 0, Finset.mem_insert_self _ _⟩ &&
        !assignment ⟨Sum.inl visible,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ then 1 else 0

@[simp]
theorem boostedPointPenalty_eval
    {n : Nat} (visible : Fin n)
    (joint : Assignment (Sum (Fin n) (Fin 1))) :
    (boostedPointPenalty visible).eval joint =
      if joint (Sum.inr 0) && !joint (Sum.inl visible) then 1 else 0 :=
  rfl

/-- All pairwise implication penalties. -/
noncomputable def boostedPointLiftedTerms (n : Nat) :
    List (LocalEnergyTerm (Sum (Fin n) (Fin 1))) :=
  Finset.univ.toList.map boostedPointPenalty

theorem boostedPointLiftedTerms_respect_two (n : Nat) :
    LocalEnergyTermsRespectK 2 (boostedPointLiftedTerms n) := by
  intro term hTerm
  simp only [boostedPointLiftedTerms, List.mem_map] at hTerm
  rcases hTerm with ⟨visible, _hVisible, rfl⟩
  simp [boostedPointPenalty]

theorem localEnergyEval_boostedPointLiftedTerms
    {n : Nat} (joint : Assignment (Sum (Fin n) (Fin 1))) :
    localEnergyEval (boostedPointLiftedTerms n) joint =
      (boostedPointViolationCount joint : ℝ) := by
  classical
  simp [localEnergyEval, boostedPointLiftedTerms,
    boostedPointViolationCount, boostedPointViolation]

theorem boostedPointLiftedTerms_nonnegative
    {n : Nat} (joint : Assignment (Sum (Fin n) (Fin 1))) :
    0 ≤ localEnergyEval (boostedPointLiftedTerms n) joint := by
  rw [localEnergyEval_boostedPointLiftedTerms]
  positivity

theorem boostedPointLiftedSet_is_groundSpace
    {n : Nat} (joint : Assignment (Sum (Fin n) (Fin 1))) :
    joint ∈ boostedPointLiftedSet n ↔
      localEnergyEval (boostedPointLiftedTerms n) joint = 0 := by
  rw [localEnergyEval_boostedPointLiftedTerms]
  rw [Nat.cast_eq_zero]
  rw [boostedPointViolationCount_eq_zero_iff]
  simp [boostedPointLiftedSet]

theorem boostedPointLifted_isMarginalModel (n : Nat) :
    IsMarginalModel (boostedPointDistribution n)
      (uniformOn (boostedPointLiftedSet n)
        (boostedPointLiftedSet_nonempty n)) := by
  classical
  apply PMF.ext
  intro visible
  refine (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      ((uniformOn (boostedPointLiftedSet n)
        (boostedPointLiftedSet_nonempty n)).map projectObs) visible)
    (PMF.apply_ne_top (boostedPointDistribution n) visible)).mp ?_
  rw [map_projectObs_apply_toReal]
  rw [boostedPointDistribution_apply_toReal]
  have hJointWeight : ∀ latent : Assignment (Fin 1),
      ((uniformOn (boostedPointLiftedSet n)
          (boostedPointLiftedSet_nonempty n))
        (jointAssignment visible latent)).toReal =
      if jointAssignment visible latent ∈ boostedPointLiftedSet n then
        (boostedPointBaseWeightRat n : ℝ) else 0 := by
    intro latent
    by_cases hMember :
        jointAssignment visible latent ∈ boostedPointLiftedSet n
    · rw [uniformOn_apply_of_mem (boostedPointLiftedSet_nonempty n) hMember,
        boostedPointLiftedSet_card]
      rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
      simp [boostedPointBaseWeightRat, hMember]
    · rw [uniformOn_apply_of_notMem
        (boostedPointLiftedSet_nonempty n) hMember]
      simp [hMember]
  simp_rw [hJointWeight]
  have hCast := congrArg (fun value : ℚ => (value : ℝ))
    (boostedPointLifted_fiber_weight n visible)
  push_cast at hCast
  have hTermCast : ∀ latent : Assignment (Fin 1),
      (((if jointAssignment visible latent ∈ boostedPointLiftedSet n then
          boostedPointBaseWeightRat n else 0) : ℚ) : ℝ) =
        if jointAssignment visible latent ∈ boostedPointLiftedSet n then
          (boostedPointBaseWeightRat n : ℝ) else 0 := by
    intro latent
    split <;> norm_num
  simp_rw [hTermCast] at hCast
  simpa [boostedPointWeights] using hCast

/-- One hidden bit suffices already at locality two. -/
theorem boostedPointDistribution_has_oneHidden_twoLocalization (n : Nat) :
    HasKLocalizationBits 2 1 n (boostedPointDistribution n) :=
  hasKLocalizationBits_of_localEnergyGroundStates
    (boostedPointLiftedSet n) (boostedPointLiftedSet_nonempty n)
    (boostedPointLiftedTerms n) (boostedPointLiftedTerms_respect_two n)
    boostedPointLiftedTerms_nonnegative
    boostedPointLiftedSet_is_groundSpace
    (boostedPointLifted_isMarginalModel n)

theorem boostedPointDistribution_has_oneHidden
    {k n : Nat} (hk : 2 ≤ k) :
    HasKLocalizationBits k 1 n (boostedPointDistribution n) :=
  hasKLocalizationBits_mono hk
    (boostedPointDistribution_has_oneHidden_twoLocalization n)

/-- Exact uniform complexity throughout the nontrivial range. -/
theorem boostedPoint_localizationComplexity_eq_one
    {k n : Nat} (hk : 2 ≤ k) (hSize : k < n) :
    localizationComplexityBits k n (boostedPointDistribution n) = 1 := by
  have hUpper := localizationComplexityBits_min k n
    (boostedPointDistribution n) 1
      (boostedPointDistribution_has_oneHidden hk)
  have hLower := boostedPoint_localizationComplexity_pos hk hSize
  omega

end KLocality
