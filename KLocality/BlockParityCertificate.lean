import KLocality.BlockParityAgreementWitness
import KLocality.LatentPadding

namespace KLocality

open scoped BigOperators

/-!
# Compiling the canonical block-parity trade

This file translates the numerical histogram collision into the paper's
boundary-safe `MarginalTradeCertificate` API.
-/

/-- The actual finite subset represented by a numerical subset code. -/
def blockParitySelectedCandidates
    (q : Nat) (subset : BlockParitySubsetCode q) :
    Finset (BlockParityCandidateCode q) :=
  Finset.univ.filter fun candidate =>
    blockParitySubsetContains subset candidate = true

@[simp]
theorem mem_blockParitySelectedCandidates
    (q : Nat) (subset : BlockParitySubsetCode q)
    (candidate : BlockParityCandidateCode q) :
    candidate ∈ blockParitySelectedCandidates q subset ↔
      blockParitySubsetContains subset candidate = true := by
  simp [blockParitySelectedCandidates]

/-- Expanded joint profile multiset for an ordinary finite candidate set. -/
def blockParityExpansion
    (q latentBits : Nat)
    (candidates : Finset (BlockParityCandidateCode q)) :
    Multiset (BlockParityNatProfile q latentBits) :=
  ((Finset.univ : Finset
      (candidates × BlockParityLatentLabeling q latentBits))).val.map
    (fun expanded =>
      blockParityNatProfile q latentBits
        (liftTuple
          (blockParityCandidateTuple q expanded.1.1) expanded.2))

theorem blockParityExpansion_card
    (q latentBits : Nat)
    (candidates : Finset (BlockParityCandidateCode q)) :
    (blockParityExpansion q latentBits candidates).card =
      candidates.card * 2 ^ (latentBits * blockParityDegree q) := by
  simp only [blockParityExpansion, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
    blockParityLatentLabeling_card]

/-- The numerical histogram coordinate is precisely the count in the
subtype-indexed expansion multiset. -/
theorem blockParityExpansion_count_eq_subsetProfileCount
    (q latentBits : Nat) (subset : BlockParitySubsetCode q)
    (profile : BlockParityNatProfile q latentBits) :
    (blockParityExpansion q latentBits
        (blockParitySelectedCandidates q subset)).count profile =
      blockParitySubsetProfileCount q latentBits subset profile := by
  classical
  unfold blockParityExpansion blockParitySubsetProfileCount
  rw [Multiset.count_map]
  rw [← Finset.filter_val]
  rw [Finset.card_val]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rw [show
    (∑ candidate : blockParitySelectedCandidates q subset,
      ∑ latent : BlockParityLatentLabeling q latentBits,
        if profile = blockParityNatProfile q latentBits
            (liftTuple
              (blockParityCandidateTuple q candidate.1) latent) then
          1 else 0) =
      ∑ candidate ∈ blockParitySelectedCandidates q subset,
        ∑ latent : BlockParityLatentLabeling q latentBits,
          if profile = blockParityNatProfile q latentBits
              (liftTuple
                (blockParityCandidateTuple q candidate) latent) then
            1 else 0 from
    Finset.sum_coe_sort (blockParitySelectedCandidates q subset)
      (fun candidate =>
        ∑ latent : BlockParityLatentLabeling q latentBits,
          if profile = blockParityNatProfile q latentBits
              (liftTuple
                (blockParityCandidateTuple q candidate) latent) then
            1 else 0)]
  unfold blockParitySelectedCandidates
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro candidate _
  by_cases hSelected : blockParitySubsetContains subset candidate = true
  · rw [if_pos hSelected, if_pos hSelected]
    unfold blockParityColumn
    rw [Multiset.count_map]
    rw [← Finset.filter_val]
    rw [Finset.card_val, Finset.card_eq_sum_ones]
    rw [Finset.sum_filter]
  · rw [if_neg hSelected, if_neg hSelected]

theorem blockParityExpansion_eq_of_histogram_eq
    {q latentBits : Nat} {left right : BlockParitySubsetCode q}
    (hHistogram :
      blockParitySubsetHistogram q latentBits left =
        blockParitySubsetHistogram q latentBits right) :
    blockParityExpansion q latentBits
        (blockParitySelectedCandidates q left) =
      blockParityExpansion q latentBits
        (blockParitySelectedCandidates q right) := by
  apply Multiset.ext.mpr
  intro profile
  rw [blockParityExpansion_count_eq_subsetProfileCount,
    blockParityExpansion_count_eq_subsetProfileCount]
  exact Fin.ext_iff.mp (congrFun hHistogram profile)

theorem blockParityCanonicalExpansion_eq
    (q : Nat) (hq : 64 ≤ q) :
    blockParityExpansion q (blockParityHiddenBudget q)
        (blockParitySelectedCandidates q
          (blockParityCanonicalCollision q hq).1) =
      blockParityExpansion q (blockParityHiddenBudget q)
        (blockParitySelectedCandidates q
          (blockParityCanonicalCollision q hq).2) :=
  blockParityExpansion_eq_of_histogram_eq
    (blockParityCanonicalCollision_histogram_eq q hq)

theorem blockParitySelectedCandidates_injective (q : Nat) :
    Function.Injective (blockParitySelectedCandidates q) := by
  intro left right hSelected
  apply blockParitySubsetContains_injective q
  funext candidate
  apply Bool.eq_iff_iff.mpr
  simp only [← mem_blockParitySelectedCandidates]
  rw [hSelected]

theorem blockParityCanonicalSelectedCandidates_ne
    (q : Nat) (hq : 64 ≤ q) :
    blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).1 ≠
      blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).2 := by
  intro hEqual
  exact blockParityCanonicalCollision_ne q hq
    (blockParitySelectedCandidates_injective q hEqual)

theorem blockParityCanonicalSelectedCandidates_card_eq
    (q : Nat) (hq : 64 ≤ q) :
    (blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).1).card =
      (blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).2).card := by
  have hCard := congrArg Multiset.card
    (blockParityCanonicalExpansion_eq q hq)
  rw [blockParityExpansion_card, blockParityExpansion_card] at hCard
  exact Nat.mul_right_cancel (by positivity) hCard

abbrev blockParityCanonicalTermCount
    (q : Nat) (hq : 64 ≤ q) : Nat :=
  (blockParitySelectedCandidates q
    (blockParityCanonicalCollision q hq).1).card

noncomputable def blockParityPositiveEnumeration
    (q : Nat) (hq : 64 ≤ q) :
    Fin (blockParityCanonicalTermCount q hq) ≃
      blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).1 :=
  (blockParitySelectedCandidates q
    (blockParityCanonicalCollision q hq).1).equivFin.symm

noncomputable def blockParityNegativeEnumeration
    (q : Nat) (hq : 64 ≤ q) :
    Fin (blockParityCanonicalTermCount q hq) ≃
      blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).2 :=
  (finCongr (blockParityCanonicalSelectedCandidates_card_eq q hq)).trans
    (blockParitySelectedCandidates q
      (blockParityCanonicalCollision q hq).2).equivFin.symm

theorem enumeratedProfileMultiset_eq_blockParityExpansion
    {q latentBits termCount : Nat}
    (candidates : Finset (BlockParityCandidateCode q))
    (enumeration : Fin termCount ≃ candidates) :
    ((Finset.univ : Finset
        (Fin termCount × BlockParityLatentLabeling q latentBits)).val.map
      (fun expanded => tupleFeatureProfile 3 (blockParityDegree q)
        (liftTuple
          (blockParityCandidateTuple q (enumeration expanded.1).1)
          expanded.2))) =
      (blockParityExpansion q latentBits candidates).map
        blockParityProfileToRat := by
  classical
  simp_rw [tupleFeatureProfile_eq_blockParityProfileToRat]
  unfold blockParityExpansion
  rw [Multiset.map_map]
  let pairEquivalence :
      (Fin termCount × BlockParityLatentLabeling q latentBits) ≃
        (candidates × BlockParityLatentLabeling q latentBits) :=
    Equiv.prodCongr enumeration (Equiv.refl _)
  let profileFunction :
      candidates × BlockParityLatentLabeling q latentBits ->
        (BlockParityJointScope q latentBits -> ℚ) :=
    fun expanded => blockParityProfileToRat
      (blockParityNatProfile q latentBits
        (liftTuple
          (blockParityCandidateTuple q expanded.1.1) expanded.2))
  simpa only [pairEquivalence, profileFunction, Function.comp_apply]
    using univ_val_map_comp_equiv pairEquivalence profileFunction

/-- The canonical histogram collision compiled into the paper's exact,
boundary-safe cubic marginal-trade format. -/
noncomputable def blockParityCanonicalCertificate
    (q : Nat) (hq : 64 ≤ q) :
    MarginalTradeCertificate 3 (blockParityDegree q)
      (blockParityCanonicalTermCount q hq)
      (BlockParityVar q) (Fin (blockParityHiddenBudget q)) where
  positive := fun term => blockParityCandidateTuple q
    (blockParityPositiveEnumeration q hq term).1
  negative := fun term => blockParityCandidateTuple q
    (blockParityNegativeEnumeration q hq term).1
  profileBalance := by
    rw [enumeratedProfileMultiset_eq_blockParityExpansion
      (blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).1)
      (blockParityPositiveEnumeration q hq)]
    rw [enumeratedProfileMultiset_eq_blockParityExpansion
      (blockParitySelectedCandidates q
        (blockParityCanonicalCollision q hq).2)
      (blockParityNegativeEnumeration q hq)]
    rw [blockParityCanonicalExpansion_eq q hq]

/-! ## The detected full-support rational distribution -/

def blockParityVisiblePrefix
    {q : Nat} (visible : Assignment (BlockParityVar q)) : BitVec q :=
  fun coordinate => visible (Sum.inl coordinate)

def blockParityVisibleSuffix
    {q : Nat} (visible : Assignment (BlockParityVar q)) : BitVec 4 :=
  fun coordinate => visible (Sum.inr (Sum.inl coordinate))

def blockParityVisibleMarker
    {q : Nat} (visible : Assignment (BlockParityVar q)) : Bool :=
  visible (Sum.inr (Sum.inr 0))

/-- Boolean indicator of the block-parity set `C_test`. -/
def blockParityVisibleTest
    {q : Nat} (test : BitVec q -> Bool)
    (visible : Assignment (BlockParityVar q)) : Bool :=
  !blockParityVisibleMarker visible &&
    (parityFour (blockParityVisibleSuffix visible) ==
      test (blockParityVisiblePrefix visible))

@[simp]
theorem blockParityVisibleTest_state
    {q : Nat} (test : BitVec q -> Bool)
    (label : BitVec q) (suffix : BitVec 4) :
    blockParityVisibleTest test (blockParityState label suffix) =
      decide (parityFour suffix = test label) := by
  change (!false && (parityFour suffix == test label)) =
    decide (parityFour suffix = test label)
  cases hParity : parityFour suffix <;>
    cases hTest : test label <;> simp

/-- Number of factors of candidate `s` which lie in the test set `C_t`. -/
def blockParityCandidateTrueCount
    {q : Nat} (test : BitVec q -> Bool)
    (candidate : BlockParityCandidateCode q) : Nat :=
  ∑ index : Fin (blockParityDegree q),
    if blockParityVisibleTest test
        (blockParityCandidateTuple q candidate index) then 1 else 0

theorem blockParityCandidateTrueCount_eq
    {q : Nat} (test : BitVec q -> Bool)
    (candidate : BlockParityCandidateCode q) :
    blockParityCandidateTrueCount test candidate =
      8 * binaryAgreementCount
        (blockParityTableVector test)
        (blockParityCandidateVectorEquiv q candidate) := by
  classical
  unfold blockParityCandidateTrueCount
  rw [← (blockParityIndexEquiv q).sum_comp]
  rw [Fintype.sum_prod_type]
  unfold binaryAgreementCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro block _
  rw [blockParityCandidateVectorEquiv_apply]
  simp only [blockParityCandidateTuple_index, blockParityVisibleTest_state,
    parityFour_parityCompletion,
    blockParityTruthTable_binaryAssignment]
  by_cases hEqual :
      binaryAssignment (blockParityPrefixCount q) candidate.val block =
        test (binaryAssignment q block.val)
  · simp [hEqual, blockParityTableVector]
  · simp [hEqual, Ne.symm hEqual, blockParityTableVector]

theorem blockParityCandidateTrueCount_eq_eight_mul_agreement
    {q : Nat} (test : BitVec q -> Bool)
    (candidate : BlockParityCandidateCode q) :
    blockParityCandidateTrueCount test candidate =
      8 * (blockParityPrefixCount q -
        blockParityHammingDistance
          (blockParityTruthTable candidate) test) := by
  rw [blockParityCandidateTrueCount_eq,
    blockParityCandidateVectorEquiv_apply,
    binaryAgreementCount_tableVector_eq]
  rw [blockParityHammingDistance_comm]

/-- Product of the unnormalized two-level weights on a candidate tuple. -/
theorem prod_blockParityVisibleTest_unnormalized
    {q : Nat} (test : BitVec q -> Bool)
    (candidate : BlockParityCandidateCode q) :
    (∏ index : Fin (blockParityDegree q),
      (if blockParityVisibleTest test
          (blockParityCandidateTuple q candidate index)
        then (2 : ℚ) else 1)) =
      (256 : ℚ) ^ (blockParityPrefixCount q -
        blockParityHammingDistance
          (blockParityTruthTable candidate) test) := by
  calc
    (∏ index : Fin (blockParityDegree q),
        (if blockParityVisibleTest test
            (blockParityCandidateTuple q candidate index)
          then (2 : ℚ) else 1)) =
        (2 : ℚ) ^ blockParityCandidateTrueCount test candidate := by
      unfold blockParityCandidateTrueCount
      calc
        _ = ∏ index : Fin (blockParityDegree q),
            (2 : ℚ) ^
              (if blockParityVisibleTest test
                  (blockParityCandidateTuple q candidate index)
                then 1 else 0) := by
              apply Finset.prod_congr rfl
              intro index _
              split <;> norm_num
        _ = _ := by
          simpa using Finset.prod_pow_eq_pow_sum
            (Finset.univ : Finset (Fin (blockParityDegree q)))
            (fun index =>
              if blockParityVisibleTest test
                  (blockParityCandidateTuple q candidate index)
                then 1 else 0) (2 : ℚ)
    _ = (2 : ℚ) ^ (8 * (blockParityPrefixCount q -
          blockParityHammingDistance
            (blockParityTruthTable candidate) test)) := by
      rw [blockParityCandidateTrueCount_eq_eight_mul_agreement]
    _ = (256 : ℚ) ^ (blockParityPrefixCount q -
          blockParityHammingDistance
            (blockParityTruthTable candidate) test) := by
      rw [pow_mul]
      norm_num

/-- Sum of the `256`-agreement weights over one encoded candidate subset. -/
def blockParitySubsetAgreementSum
    (q : Nat) (subset : BlockParitySubsetCode q)
    (test : BitVec q -> Bool) : Nat :=
  ∑ candidate : BlockParityCandidateCode q,
    if blockParitySubsetContains subset candidate then
      256 ^ (blockParityPrefixCount q -
        blockParityHammingDistance
          (blockParityTruthTable candidate) test)
    else 0

theorem blockParityAgreementObjective_eq_sub
    (q : Nat) (hq : 64 ≤ q) (test : BitVec q -> Bool) :
    blockParityAgreementObjective q hq test =
      (blockParitySubsetAgreementSum q
          (blockParityCanonicalCollision q hq).1 test : ℤ) -
        (blockParitySubsetAgreementSum q
          (blockParityCanonicalCollision q hq).2 test : ℤ) := by
  unfold blockParityAgreementObjective blockParityTradeCoefficient
  rw [← (blockParityCandidateEquiv q).sum_comp]
  unfold blockParityTradeCoefficientCode blockParitySubsetAgreementSum
  simp only [blockParityCandidateEquiv_apply,
    blockParityTruthTableCode_truthTable, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro candidate _ <;>
    split <;> simp

theorem blockParityCanonicalSubsetAgreementSum_ne
    (q : Nat) (hq : 64 ≤ q) :
    blockParitySubsetAgreementSum q
        (blockParityCanonicalCollision q hq).1
        (blockParityCanonicalTest q hq) ≠
      blockParitySubsetAgreementSum q
        (blockParityCanonicalCollision q hq).2
        (blockParityCanonicalTest q hq) := by
  intro hEqual
  apply blockParityAgreementObjective_canonical_ne_zero q hq
  rw [blockParityAgreementObjective_eq_sub, hEqual, sub_self]

/-- Unnormalized rational table of the canonical Boolean tilt. -/
def blockParityCanonicalUnnormalizedRat
    (q : Nat) (hq : 64 ≤ q)
    (visible : Assignment (BlockParityVar q)) : ℚ :=
  if blockParityVisibleTest (blockParityCanonicalTest q hq) visible then 2 else 1

noncomputable def blockParityCanonicalNormalizerRat
    (q : Nat) (hq : 64 ≤ q) : ℚ :=
  ∑ visible : Assignment (BlockParityVar q),
    blockParityCanonicalUnnormalizedRat q hq visible

theorem blockParityCanonicalUnnormalizedRat_pos
    (q : Nat) (hq : 64 ≤ q)
    (visible : Assignment (BlockParityVar q)) :
    0 < blockParityCanonicalUnnormalizedRat q hq visible := by
  unfold blockParityCanonicalUnnormalizedRat
  split <;> norm_num

theorem blockParityCanonicalNormalizerRat_pos
    (q : Nat) (hq : 64 ≤ q) :
    0 < blockParityCanonicalNormalizerRat q hq := by
  classical
  unfold blockParityCanonicalNormalizerRat
  exact Finset.sum_pos
    (fun visible _ => blockParityCanonicalUnnormalizedRat_pos q hq visible)
    Finset.univ_nonempty

noncomputable def blockParityCanonicalWeightsRat
    (q : Nat) (hq : 64 ≤ q)
    (visible : Assignment (BlockParityVar q)) : ℚ :=
  blockParityCanonicalUnnormalizedRat q hq visible /
    blockParityCanonicalNormalizerRat q hq

noncomputable def blockParityCanonicalWeights
    (q : Nat) (hq : 64 ≤ q)
    (visible : Assignment (BlockParityVar q)) : ℝ :=
  blockParityCanonicalWeightsRat q hq visible

theorem blockParityCanonicalWeightsRat_pos
    (q : Nat) (hq : 64 ≤ q)
    (visible : Assignment (BlockParityVar q)) :
    0 < blockParityCanonicalWeightsRat q hq visible :=
  div_pos (blockParityCanonicalUnnormalizedRat_pos q hq visible)
    (blockParityCanonicalNormalizerRat_pos q hq)

theorem sum_blockParityCanonicalWeightsRat
    (q : Nat) (hq : 64 ≤ q) :
    (∑ visible : Assignment (BlockParityVar q),
      blockParityCanonicalWeightsRat q hq visible) = 1 := by
  classical
  unfold blockParityCanonicalWeightsRat blockParityCanonicalNormalizerRat
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos
    (fun visible _ => blockParityCanonicalUnnormalizedRat_pos q hq visible)
    Finset.univ_nonempty))

/-- Explicit full-support rational law detected by the canonical trade. -/
noncomputable def blockParityCanonicalDistribution
    (q : Nat) (hq : 64 ≤ q) :
    Distribution (Assignment (BlockParityVar q)) :=
  distributionOfRealWeights (blockParityCanonicalWeights q hq)
    (fun visible => Rat.cast_nonneg.mpr
      (blockParityCanonicalWeightsRat_pos q hq visible).le)
    (by
      have hCast := congrArg (fun value : ℚ => (value : ℝ))
        (sum_blockParityCanonicalWeightsRat q hq)
      simpa [blockParityCanonicalWeights, Rat.cast_sum] using hCast)

@[simp]
theorem blockParityCanonicalDistribution_apply_toReal
    (q : Nat) (hq : 64 ≤ q)
    (visible : Assignment (BlockParityVar q)) :
    (blockParityCanonicalDistribution q hq visible).toReal =
      blockParityCanonicalWeights q hq visible := by
  exact distributionOfRealWeights_apply_toReal _ _ _ visible

theorem blockParityCanonicalDistribution_support
    (q : Nat) (hq : 64 ≤ q) :
    (blockParityCanonicalDistribution q hq).support = Set.univ := by
  ext visible
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff
    (blockParityCanonicalDistribution q hq) visible).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [blockParityCanonicalDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  exact (ne_of_gt (Rat.cast_pos.mpr
    (blockParityCanonicalWeightsRat_pos q hq visible))) hReal

theorem prod_blockParityCanonicalWeightsRat_candidateTuple
    (q : Nat) (hq : 64 ≤ q)
    (candidate : BlockParityCandidateCode q) :
    (∏ index : Fin (blockParityDegree q),
      blockParityCanonicalWeightsRat q hq
        (blockParityCandidateTuple q candidate index)) =
      (256 : ℚ) ^ (blockParityPrefixCount q -
          blockParityHammingDistance
            (blockParityTruthTable candidate)
            (blockParityCanonicalTest q hq)) /
        blockParityCanonicalNormalizerRat q hq ^ blockParityDegree q := by
  unfold blockParityCanonicalWeightsRat
  rw [Finset.prod_div_distrib]
  rw [show
    (∏ index : Fin (blockParityDegree q),
      blockParityCanonicalUnnormalizedRat q hq
        (blockParityCandidateTuple q candidate index)) =
      (256 : ℚ) ^ (blockParityPrefixCount q -
        blockParityHammingDistance
          (blockParityTruthTable candidate)
          (blockParityCanonicalTest q hq)) by
    simpa [blockParityCanonicalUnnormalizedRat] using
      prod_blockParityVisibleTest_unnormalized
        (blockParityCanonicalTest q hq) candidate]
  simp

theorem prod_blockParityCanonicalWeights_candidateTuple
    (q : Nat) (hq : 64 ≤ q)
    (candidate : BlockParityCandidateCode q) :
    (∏ index : Fin (blockParityDegree q),
      blockParityCanonicalWeights q hq
        (blockParityCandidateTuple q candidate index)) =
      (256 : ℝ) ^ (blockParityPrefixCount q -
          blockParityHammingDistance
            (blockParityTruthTable candidate)
            (blockParityCanonicalTest q hq)) /
        (blockParityCanonicalNormalizerRat q hq : ℝ) ^
          blockParityDegree q := by
  have hRat := prod_blockParityCanonicalWeightsRat_candidateTuple
    q hq candidate
  have hReal := congrArg (fun value : ℚ => (value : ℝ)) hRat
  simpa [blockParityCanonicalWeights, Rat.cast_prod,
    Rat.cast_div, Rat.cast_pow] using hReal

theorem sum_prod_blockParityCanonicalWeights_of_equiv
    {q termCount : Nat} (hq : 64 ≤ q)
    (subset : BlockParitySubsetCode q)
    (enumeration : Fin termCount ≃
      blockParitySelectedCandidates q subset) :
    (∑ term : Fin termCount,
      ∏ index : Fin (blockParityDegree q),
        blockParityCanonicalWeights q hq
          (blockParityCandidateTuple q (enumeration term).1 index)) =
      (blockParitySubsetAgreementSum q subset
          (blockParityCanonicalTest q hq) : ℝ) /
        (blockParityCanonicalNormalizerRat q hq : ℝ) ^
          blockParityDegree q := by
  classical
  simp_rw [prod_blockParityCanonicalWeights_candidateTuple]
  rw [← Finset.sum_div]
  congr 1
  calc
    (∑ term : Fin termCount,
        (256 : ℝ) ^ (blockParityPrefixCount q -
          blockParityHammingDistance
            (blockParityTruthTable (enumeration term).1)
            (blockParityCanonicalTest q hq))) =
        ∑ candidate : blockParitySelectedCandidates q subset,
          (256 : ℝ) ^ (blockParityPrefixCount q -
            blockParityHammingDistance
              (blockParityTruthTable candidate.1)
              (blockParityCanonicalTest q hq)) := by
      exact enumeration.sum_comp (fun candidate =>
        (256 : ℝ) ^ (blockParityPrefixCount q -
          blockParityHammingDistance
            (blockParityTruthTable candidate.1)
            (blockParityCanonicalTest q hq)))
    _ = ∑ candidate ∈ blockParitySelectedCandidates q subset,
          (256 : ℝ) ^ (blockParityPrefixCount q -
            blockParityHammingDistance
              (blockParityTruthTable candidate)
              (blockParityCanonicalTest q hq)) := by
      exact Finset.sum_coe_sort (blockParitySelectedCandidates q subset)
        (fun candidate =>
          (256 : ℝ) ^ (blockParityPrefixCount q -
            blockParityHammingDistance
              (blockParityTruthTable candidate)
              (blockParityCanonicalTest q hq)))
    _ = (blockParitySubsetAgreementSum q subset
          (blockParityCanonicalTest q hq) : ℝ) := by
      unfold blockParitySelectedCandidates blockParitySubsetAgreementSum
      rw [Finset.sum_filter]
      push_cast
      rfl

theorem blockParityCanonicalCertificate_positiveValue
    (q : Nat) (hq : 64 ≤ q) :
    (blockParityCanonicalCertificate q hq).positiveValue
        (blockParityCanonicalWeights q hq) =
      (blockParitySubsetAgreementSum q
          (blockParityCanonicalCollision q hq).1
          (blockParityCanonicalTest q hq) : ℝ) /
        (blockParityCanonicalNormalizerRat q hq : ℝ) ^
          blockParityDegree q := by
  simpa [MarginalTradeCertificate.positiveValue,
    blockParityCanonicalCertificate] using
    sum_prod_blockParityCanonicalWeights_of_equiv hq
      (blockParityCanonicalCollision q hq).1
      (blockParityPositiveEnumeration q hq)

theorem blockParityCanonicalCertificate_negativeValue
    (q : Nat) (hq : 64 ≤ q) :
    (blockParityCanonicalCertificate q hq).negativeValue
        (blockParityCanonicalWeights q hq) =
      (blockParitySubsetAgreementSum q
          (blockParityCanonicalCollision q hq).2
          (blockParityCanonicalTest q hq) : ℝ) /
        (blockParityCanonicalNormalizerRat q hq : ℝ) ^
          blockParityDegree q := by
  simpa [MarginalTradeCertificate.negativeValue,
    blockParityCanonicalCertificate] using
    sum_prod_blockParityCanonicalWeights_of_equiv hq
      (blockParityCanonicalCollision q hq).2
      (blockParityNegativeEnumeration q hq)

theorem blockParityCanonicalCertificate_detects
    (q : Nat) (hq : 64 ≤ q) :
    (blockParityCanonicalCertificate q hq).positiveValue
        (fun visible =>
          (blockParityCanonicalDistribution q hq visible).toReal) ≠
      (blockParityCanonicalCertificate q hq).negativeValue
        (fun visible =>
          (blockParityCanonicalDistribution q hq visible).toReal) := by
  simp_rw [blockParityCanonicalDistribution_apply_toReal,
    blockParityCanonicalCertificate_positiveValue,
    blockParityCanonicalCertificate_negativeValue]
  intro hEqual
  have hDenominator :
      (blockParityCanonicalNormalizerRat q hq : ℝ) ^
          blockParityDegree q ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt
      (Rat.cast_pos.mpr (blockParityCanonicalNormalizerRat_pos q hq)))
  have hCasts := (div_left_inj' hDenominator).mp hEqual
  apply blockParityCanonicalSubsetAgreementSum_ne q hq
  exact_mod_cast hCasts

theorem blockParityVar_card (q : Nat) :
    Fintype.card (BlockParityVar q) = q + 5 := by
  simp [BlockParityVar, Fintype.card_sum, Fintype.card_fin]

/-- A literal superlinear cubic-localization lower bound for the canonical
full-support rational family.  Its visible dimension is `q+5`, while every
realization needs more than `q^2` hidden bits. -/
theorem blockParityCanonicalDistribution_localizationComplexity_gt
    (q : Nat) (hq : 64 ≤ q) :
    blockParityHiddenBudget q <
      localizationComplexity 3 (BlockParityVar q)
        (blockParityCanonicalDistribution q hq) := by
  apply localizationComplexity_gt_of_not_hasKLocalization (by norm_num)
  exact (blockParityCanonicalCertificate q hq).obstructs_localization
    (blockParityCanonicalCertificate_detects q hq)

theorem blockParityCanonicalDistribution_localizationComplexity_gt_sq
    (q : Nat) (hq : 64 ≤ q) :
    q ^ 2 < localizationComplexity 3 (BlockParityVar q)
      (blockParityCanonicalDistribution q hq) := by
  simpa [blockParityHiddenBudget] using
    blockParityCanonicalDistribution_localizationComplexity_gt q hq

/-- As a family indexed by `q`, the checked quadratic bound eventually
dominates every fixed multiple of the visible dimension `q+5`. -/
theorem blockParityCanonicalDistribution_eventually_gt_linear :
    ∀ constant : Nat, ∃ threshold : Nat, ∃ hThreshold : 64 ≤ threshold,
      ∀ q, (hq : threshold ≤ q) ->
        constant * (q + 5) <
          localizationComplexity 3 (BlockParityVar q)
            (blockParityCanonicalDistribution q
              (le_trans hThreshold hq)) := by
  intro constant
  refine ⟨max 64 (2 * constant + 6), le_max_left _ _, ?_⟩
  intro q hq
  have h64 : 64 ≤ q := le_trans (le_max_left _ _) hq
  have hGrowth : 2 * constant + 6 ≤ q :=
    le_trans (le_max_right _ _) hq
  have hLinear : constant * (q + 5) < q ^ 2 := by
    nlinarith [Nat.zero_le constant]
  exact lt_trans hLinear
    (blockParityCanonicalDistribution_localizationComplexity_gt_sq q h64)

end KLocality
