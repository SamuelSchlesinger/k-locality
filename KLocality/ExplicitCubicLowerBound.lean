import KLocality.MarginalTradeCertificate
import KLocality.UniformParityUpperBound
import KLocality.LogInteractionCertificate
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Order.Interval.Finset.Fin

namespace KLocality

open scoped BigOperators

set_option maxRecDepth 30000
set_option exponentiation.threshold 12000

/-!
# An explicit full-support law requiring two hidden bits at cubic locality

This file constructs a rational distribution on ten visible bits and proves
that it has no cubic localization with zero or one hidden bit.  The
distribution itself is elementary: its unnormalized cell weights are powers
of two.  The obstruction is obtained by pigeonholing a very large finite
family of visible monomials into the much smaller set of their expanded
one-hidden cubic feature histograms.

The intentionally generous numerical constants keep the counting argument
transparent.  They are not intended to give a practical certificate degree.
-/

/-- The digit base used to index a large family of visible monomials. -/
def cubicHardDigitBase : Nat := 2 ^ 3

/-- Binary logarithm of the candidate count. -/
def cubicHardCandidateLog : Nat := 3 * 1023

/-- Binary logarithm used to bound the profile count. -/
def cubicHardProfileLog : Nat := 13 * 232

/-- Every candidate monomial has this common degree. -/
def cubicHardDegree : Nat := 1023 * cubicHardDigitBase

/-- A candidate is a 1023-digit base-`cubicHardDigitBase` word. -/
abbrev CubicHardCandidate := Fin 1023 → Fin cubicHardDigitBase

/-- Number of candidate monomials. -/
def cubicHardCandidateCount : Nat := cubicHardDigitBase ^ 1023

/-- Number of possible order-three joint feature profiles of a tuple. -/
def cubicHardProfileCountBound : Nat := (cubicHardDegree + 1) ^ 232

theorem cubicHardDigitBase_eq : cubicHardDigitBase = 2 ^ 3 := rfl

theorem cubicHardCandidateCount_eq :
    cubicHardCandidateCount = 2 ^ cubicHardCandidateLog := by
  unfold cubicHardCandidateCount cubicHardDigitBase cubicHardCandidateLog
  exact (pow_mul 2 3 1023).symm

theorem cubicHardDegree_lt_two_pow_13 : cubicHardDegree < 2 ^ 13 := by
  norm_num [cubicHardDegree, cubicHardDigitBase]

theorem cubicHardDegree_add_one_le_two_pow_13 :
    cubicHardDegree + 1 ≤ 2 ^ 13 := by
  exact Nat.succ_le_iff.mpr cubicHardDegree_lt_two_pow_13

theorem cubicHardProfileCountBound_le :
    cubicHardProfileCountBound ≤ 2 ^ cubicHardProfileLog := by
  unfold cubicHardProfileCountBound
  calc
    (cubicHardDegree + 1) ^ 232 ≤ (2 ^ 13) ^ 232 :=
      Nat.pow_le_pow_left cubicHardDegree_add_one_le_two_pow_13 232
    _ = 2 ^ (13 * 232) := (pow_mul 2 13 232).symm
    _ = 2 ^ cubicHardProfileLog := rfl

theorem two_pow_mul_two_pow_add_one_le (left right : Nat) :
    2 ^ left * 2 ^ right + 1 ≤ 2 ^ (right + left + 1) := by
  have hPositive : 0 < 2 ^ left * 2 ^ right := by positivity
  calc
    2 ^ left * 2 ^ right + 1 ≤
        2 ^ left * 2 ^ right + 2 ^ left * 2 ^ right :=
      Nat.add_le_add_left hPositive _
    _ = (2 ^ left * 2 ^ right) * 2 := (Nat.mul_two _).symm
    _ = 2 ^ (left + right) * 2 := by rw [pow_add]
    _ = 2 ^ (left + right + 1) := by rw [pow_succ]
    _ = 2 ^ (right + left + 1) := by
      congr 1
      omega

theorem mul_two_pow_add_one_le
    {count log : Nat} (right : Nat) (hCount : count ≤ 2 ^ log) :
    count * 2 ^ right + 1 ≤ 2 ^ (right + log + 1) := by
  calc
    count * 2 ^ right + 1 ≤ 2 ^ log * 2 ^ right + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hCount) 1
    _ ≤ 2 ^ (right + log + 1) :=
      two_pow_mul_two_pow_add_one_le _ _

theorem cubicHardExpansionCount_lt_coordinateBound :
    cubicHardCandidateCount * 2 ^ cubicHardDegree <
      2 ^ (cubicHardDegree + cubicHardCandidateLog + 1) := by
  apply lt_of_lt_of_le (Nat.lt_succ_self _)
  exact mul_two_pow_add_one_le _ cubicHardCandidateCount_eq.le

theorem cubicHardCandidateLog_add_one_lt_two_pow_13 :
    cubicHardCandidateLog + 1 < 2 ^ 13 := by
  norm_num [cubicHardCandidateLog]

theorem cubicHardDegree_add_candidateLog_lt_two_pow_14 :
    cubicHardDegree + cubicHardCandidateLog + 1 < 2 ^ 14 := by
  calc
    cubicHardDegree + cubicHardCandidateLog + 1 =
        cubicHardDegree + (cubicHardCandidateLog + 1) := by omega
    _ < 2 ^ 13 + 2 ^ 13 := Nat.add_lt_add
      cubicHardDegree_lt_two_pow_13
      cubicHardCandidateLog_add_one_lt_two_pow_13
    _ = 2 ^ 14 := by norm_num [pow_succ']

theorem cubicHardProfileLog_add_14_lt_candidateLog :
    cubicHardProfileLog + 14 < cubicHardCandidateLog := by
  norm_num [cubicHardProfileLog, cubicHardCandidateLog]

theorem cubicHardProfileExponent_lt_candidateCount :
    cubicHardProfileCountBound *
        (cubicHardDegree + cubicHardCandidateLog + 1) <
      cubicHardCandidateCount := by
  rw [cubicHardCandidateCount_eq]
  calc
    cubicHardProfileCountBound *
        (cubicHardDegree + cubicHardCandidateLog + 1) <
        2 ^ cubicHardProfileLog * 2 ^ 14 :=
      Nat.mul_lt_mul_of_le_of_lt cubicHardProfileCountBound_le
        cubicHardDegree_add_candidateLog_lt_two_pow_14 (by positivity)
    _ = 2 ^ (cubicHardProfileLog + 14) := by rw [pow_add]
    _ < 2 ^ cubicHardCandidateLog :=
      Nat.pow_lt_pow_right (by omega)
        cubicHardProfileLog_add_14_lt_candidateLog

theorem pow_lt_two_pow_of_le_two_pow
    {value exponent log upper : Nat}
    (hValue : value ≤ 2 ^ log)
    (hExponent : log * exponent < upper) :
    value ^ exponent < 2 ^ upper := by
  calc
    value ^ exponent ≤ (2 ^ log) ^ exponent :=
      Nat.pow_le_pow_left hValue exponent
    _ = 2 ^ (log * exponent) := (pow_mul 2 log exponent).symm
    _ < 2 ^ upper := Nat.pow_lt_pow_right (by omega) hExponent

/-- The powerset of candidates is larger than the space of aggregate cubic
profile histograms.  This is the sole quantitative input to pigeonhole. -/
theorem cubicHard_histogram_cardinality_bound :
    (2 ^ (cubicHardDegree + cubicHardCandidateLog + 1)) ^
        cubicHardProfileCountBound <
      2 ^ cubicHardCandidateCount := by
  apply pow_lt_two_pow_of_le_two_pow le_rfl
  rw [Nat.mul_comm]
  exact cubicHardProfileExponent_lt_candidateCount

/-! ## Candidate monomials and their codes -/

theorem cubicHardDegree_eq : cubicHardDegree = 1023 * 8 := by
  norm_num [cubicHardDegree, cubicHardDigitBase]

/-- Split the homogeneous tuple index into one of 1023 visible cells and one
of eight slots assigned to that cell. -/
def cubicHardIndexEquiv : Fin 1023 × Fin 8 ≃ Fin cubicHardDegree :=
  finProdFinEquiv.trans (finCongr cubicHardDegree_eq.symm)

/-- The first 1023 points of the ten-cube. -/
def cubicHardBlockState (block : Fin 1023) : BitVec 10 :=
  binaryAssignment 10 block.val

/-- The remaining point of the ten-cube, used as tuple filler. -/
def cubicHardFillerState : BitVec 10 :=
  binaryAssignment 10 1023

theorem cubicHardBlockState_ne_filler (block : Fin 1023) :
    cubicHardBlockState block ≠ cubicHardFillerState := by
  intro hEqual
  have hNat := congrArg binaryAssignmentValue hEqual
  rw [cubicHardBlockState,
    binaryAssignmentValue_binaryAssignment_of_lt
      (ell := 10) (value := block.val)
      (lt_trans block.isLt (by norm_num)),
    cubicHardFillerState,
    binaryAssignmentValue_binaryAssignment_of_lt
      (ell := 10) (value := 1023) (by norm_num)] at hNat
  omega

/-- The candidate's digit at `block` records how many of that block's eight
slots contain the block state; all remaining slots contain the filler. -/
def cubicHardCandidateTuple
    (candidate : CubicHardCandidate) :
    Fin cubicHardDegree → BitVec 10 :=
  fun index =>
    let blockSlot := cubicHardIndexEquiv.symm index
    if blockSlot.2 < candidate blockSlot.1 then
      cubicHardBlockState blockSlot.1
    else cubicHardFillerState

@[simp]
theorem cubicHardCandidateTuple_index
    (candidate : CubicHardCandidate) (block : Fin 1023) (slot : Fin 8) :
    cubicHardCandidateTuple candidate (cubicHardIndexEquiv (block, slot)) =
      if slot < candidate block then cubicHardBlockState block
      else cubicHardFillerState := by
  simp [cubicHardCandidateTuple]

/-- Base-8 code of a candidate.  The tuple filler has exponent zero, so only
these 1023 digits contribute to its probability monomial. -/
def cubicHardCandidateCode (candidate : CubicHardCandidate) : Nat :=
  ∑ block : Fin 1023,
    (candidate block).val * cubicHardDigitBase ^ block.val

theorem cubicHardCandidateCode_eq_ofDigits (candidate : CubicHardCandidate) :
    cubicHardCandidateCode candidate =
      Nat.ofDigits cubicHardDigitBase
        (List.ofFn fun block : Fin 1023 => (candidate block).val) := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  rfl

theorem cubicHardCandidateCode_injective :
    Function.Injective cubicHardCandidateCode := by
  intro left right hCode
  rw [cubicHardCandidateCode_eq_ofDigits,
    cubicHardCandidateCode_eq_ofDigits] at hCode
  have hDigits := Nat.ofDigits_inj_of_len_eq
    (b := cubicHardDigitBase) (by norm_num [cubicHardDigitBase])
    (by simp only [List.length_ofFn])
    (by
      intro digit hDigit
      simp only [List.mem_ofFn] at hDigit
      rcases hDigit with ⟨index, rfl⟩
      exact (left index).isLt)
    (by
      intro digit hDigit
      simp only [List.mem_ofFn] at hDigit
      rcases hDigit with ⟨index, rfl⟩
      exact (right index).isLt)
    hCode
  have hValues :
      (fun index : Fin 1023 => (left index).val) =
        fun index : Fin 1023 => (right index).val :=
    List.ofFn_inj.mp hDigits
  funext index
  exact Fin.ext (congrFun hValues index)

/-- The exponent assigned to a visible cell in the unnormalized target law.
The filler has weight one. -/
def cubicHardCellExponent (visible : BitVec 10) : Nat :=
  if visible = cubicHardFillerState then 0
  else cubicHardDigitBase ^ binaryAssignmentValue visible

@[simp]
theorem cubicHardCellExponent_filler :
    cubicHardCellExponent cubicHardFillerState = 0 := by
  simp [cubicHardCellExponent]

@[simp]
theorem cubicHardCellExponent_block (block : Fin 1023) :
    cubicHardCellExponent (cubicHardBlockState block) =
      cubicHardDigitBase ^ block.val := by
  rw [cubicHardCellExponent, if_neg (cubicHardBlockState_ne_filler block)]
  rw [cubicHardBlockState,
    binaryAssignmentValue_binaryAssignment_of_lt
      (ell := 10) (value := block.val)
      (lt_trans block.isLt (by norm_num))]

theorem sum_cubicHardCellExponent_candidateTuple
    (candidate : CubicHardCandidate) :
    (∑ index : Fin cubicHardDegree,
      cubicHardCellExponent (cubicHardCandidateTuple candidate index)) =
      cubicHardCandidateCode candidate := by
  rw [← cubicHardIndexEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  unfold cubicHardCandidateCode
  apply Finset.sum_congr rfl
  intro block _
  simp only [cubicHardCandidateTuple_index, apply_ite,
    cubicHardCellExponent_block, cubicHardCellExponent_filler]
  calc
    (∑ slot : Fin 8,
        if slot < candidate block then
          cubicHardDigitBase ^ block.val else 0) =
        ∑ slot ∈ Finset.Iio (candidate block),
          cubicHardDigitBase ^ block.val := by
      rw [← Finset.sum_filter]
      have hFilter :
          (Finset.univ.filter fun slot : Fin 8 =>
            slot < candidate block) = Finset.Iio (candidate block) := by
        ext slot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_Iio (x := slot)
          (a := candidate block)).symm
      rw [hFilter]
      rfl
    _ = (candidate block).val * cubicHardDigitBase ^ block.val := by
      rw [Finset.sum_const, Fin.card_Iio]
      rfl

/-! ## Cubic joint profiles and expansion histograms -/

abbrev CubicHardJointScope :=
  FeatureScope (Sum (Fin 10) (Fin 1)) 3

/-- Natural-valued presentation of a tuple's cubic feature profile. -/
def cubicHardNatProfile
    (tuple : Fin cubicHardDegree →
      Assignment (Sum (Fin 10) (Fin 1))) :
    CubicHardJointScope → Fin (cubicHardDegree + 1) :=
  fun scope =>
    ⟨((Finset.univ : Finset (Fin cubicHardDegree)).filter fun index =>
        scope.1 ⊆ trueCoordinates (tuple index)).card,
      Nat.lt_succ_of_le (by
        have hCard := Finset.card_filter_le
          (Finset.univ : Finset (Fin cubicHardDegree))
          (fun index => scope.1 ⊆ trueCoordinates (tuple index))
        simpa only [Finset.card_univ, Fintype.card_fin] using hCard)⟩

abbrev CubicHardNatProfile :=
  CubicHardJointScope → Fin (cubicHardDegree + 1)

/-- Cast a natural feature-count profile to the rational profile used by
`MarginalTradeCertificate`. -/
def cubicHardProfileToRat
    (profile : CubicHardNatProfile) : CubicHardJointScope → ℚ :=
  fun scope => profile scope

theorem tupleFeatureProfile_eq_cubicHardProfileToRat
    (tuple : Fin cubicHardDegree →
      Assignment (Sum (Fin 10) (Fin 1))) :
    tupleFeatureProfile 3 cubicHardDegree tuple =
      cubicHardProfileToRat (cubicHardNatProfile tuple) := by
  funext scope
  let predicate : Fin cubicHardDegree → Prop := fun index =>
    scope.1 ⊆ trueCoordinates (tuple index)
  have hCard := Finset.card_filter predicate
    (Finset.univ : Finset (Fin cubicHardDegree))
  have hCast := congrArg (fun value : Nat => (value : ℚ)) hCard
  simpa only [tupleFeatureProfile, cubicHardProfileToRat,
    cubicHardNatProfile, rationalMonomialValue, predicate,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_const_zero, Finset.sum_filter] using hCast.symm

theorem cubicHardJointScope_card :
    Fintype.card CubicHardJointScope = 232 := by
  decide

theorem cubicHardCandidate_card :
    Fintype.card CubicHardCandidate = cubicHardCandidateCount := by
  simp only [CubicHardCandidate, Fintype.card_fun, Fintype.card_fin,
    cubicHardCandidateCount]

theorem cubicHardNatProfile_card :
    Fintype.card CubicHardNatProfile = cubicHardProfileCountBound := by
  simp [CubicHardNatProfile, cubicHardProfileCountBound,
    cubicHardJointScope_card]

/-- One hidden assignment for each factor of a visible monomial. -/
abbrev CubicHardLatentLabeling :=
  Fin cubicHardDegree → Assignment (Fin 1)

theorem cubicHardLatentLabeling_card :
    Fintype.card CubicHardLatentLabeling = 2 ^ cubicHardDegree := by
  simp only [CubicHardLatentLabeling, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, pow_one]

/-- Multiset of all cubic joint profiles obtained by expanding every
candidate in a chosen subset over its one-hidden-bit fiber. -/
noncomputable def cubicHardExpansion
    (candidates : Finset CubicHardCandidate) :
    Multiset CubicHardNatProfile :=
  ((Finset.univ : Finset
      (candidates × CubicHardLatentLabeling))).val.map
    (fun expanded =>
      cubicHardNatProfile
        (liftTuple (cubicHardCandidateTuple expanded.1.1) expanded.2))

theorem cubicHardExpansion_card
    (candidates : Finset CubicHardCandidate) :
    (cubicHardExpansion candidates).card =
      candidates.card * 2 ^ cubicHardDegree := by
  simp only [cubicHardExpansion, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
    cubicHardLatentLabeling_card]

/-- One coordinate of a histogram is large enough to count every expanded
profile contributed by an arbitrary subset of candidates. -/
abbrev CubicHardHistogramCoordinate :=
  Fin (2 ^ (cubicHardDegree + cubicHardCandidateLog + 1))

abbrev CubicHardHistogram :=
  CubicHardNatProfile → CubicHardHistogramCoordinate

/-- Histogram of expanded cubic profiles, including multiplicity. -/
noncomputable def cubicHardHistogram
    (candidates : Finset CubicHardCandidate) : CubicHardHistogram :=
  fun profile =>
    ⟨(cubicHardExpansion candidates).count profile, by
      calc
        (cubicHardExpansion candidates).count profile ≤
            (cubicHardExpansion candidates).card :=
          Multiset.count_le_card _ _
        _ = candidates.card * 2 ^ cubicHardDegree :=
          cubicHardExpansion_card candidates
        _ ≤ cubicHardCandidateCount * 2 ^ cubicHardDegree := by
          apply Nat.mul_le_mul_right
          simpa only [cubicHardCandidate_card] using
            candidates.card_le_univ
        _ < 2 ^ (cubicHardDegree + cubicHardCandidateLog + 1) :=
          cubicHardExpansionCount_lt_coordinateBound⟩

theorem cubicHardHistogram_card :
    Fintype.card CubicHardHistogram =
      (2 ^ (cubicHardDegree + cubicHardCandidateLog + 1)) ^
        cubicHardProfileCountBound := by
  calc
    Fintype.card CubicHardHistogram =
        Fintype.card CubicHardHistogramCoordinate ^
          Fintype.card CubicHardNatProfile := Fintype.card_fun
    _ = Fintype.card CubicHardHistogramCoordinate ^
          cubicHardProfileCountBound := by
      rw [cubicHardNatProfile_card]
    _ = (2 ^ (cubicHardDegree + cubicHardCandidateLog + 1)) ^
          cubicHardProfileCountBound := by
      rw [Fintype.card_fin]

/-- Two distinct finite subsets of candidates have exactly the same expanded
one-hidden cubic profile multiset. -/
theorem exists_cubicHardExpansion_collision :
    ∃ left right : Finset CubicHardCandidate,
      left ≠ right ∧
        cubicHardExpansion left = cubicHardExpansion right := by
  classical
  have hCard : Fintype.card CubicHardHistogram <
      Fintype.card (Finset CubicHardCandidate) := by
    rw [cubicHardHistogram_card, Fintype.card_finset,
      cubicHardCandidate_card]
    exact cubicHard_histogram_cardinality_bound
  have hNotInjective :
      ¬Function.Injective cubicHardHistogram :=
    Fintype.not_injective_of_card_lt cubicHardHistogram hCard
  simp only [Function.Injective] at hNotInjective
  push_neg at hNotInjective
  rcases hNotInjective with ⟨left, right, hHistogram, hDistinct⟩
  refine ⟨left, right, hDistinct, ?_⟩
  apply Multiset.ext.mpr
  intro profile
  have hCoordinate := congrFun hHistogram profile
  have hValue := congrArg Fin.val hCoordinate
  simpa only [cubicHardHistogram] using hValue

theorem cubicHardExpansion_collision_card_eq
    {left right : Finset CubicHardCandidate}
    (hExpansion : cubicHardExpansion left = cubicHardExpansion right) :
    left.card = right.card := by
  have hCard := congrArg Multiset.card hExpansion
  rw [cubicHardExpansion_card, cubicHardExpansion_card] at hCard
  exact Nat.mul_right_cancel (by positivity) hCard

/-! ## The chosen marginal-trade certificate -/

/-- Reindexing the domain of a finite multiset map by an equivalence does not
change the resulting multiset. -/
theorem univ_val_map_comp_equiv
    {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (equivalence : α ≃ β) (f : β → γ) :
    ((Finset.univ : Finset α).val.map
        (fun value => f (equivalence value))) =
      (Finset.univ : Finset β).val.map f := by
  classical
  have hUniv :
      (Finset.univ : Finset α).map equivalence.toEmbedding =
        (Finset.univ : Finset β) := by
    ext value
    simp
  have hMapped := congrArg (fun values : Finset β => values.val.map f) hUniv
  simpa only [Finset.map_val, Multiset.map_map, Function.comp_apply]
    using hMapped

/-- Enumerating a candidate subset before expanding it gives the same
profile multiset as the subtype-indexed definition above. -/
theorem enumeratedProfileMultiset_eq_cubicHardExpansion
    {termCount : Nat}
    (candidates : Finset CubicHardCandidate)
    (enumeration : Fin termCount ≃ candidates) :
    ((Finset.univ : Finset
        (Fin termCount × CubicHardLatentLabeling)).val.map
      (fun expanded => tupleFeatureProfile 3 cubicHardDegree
        (liftTuple
          (cubicHardCandidateTuple (enumeration expanded.1).1)
          expanded.2))) =
      (cubicHardExpansion candidates).map cubicHardProfileToRat := by
  classical
  simp_rw [tupleFeatureProfile_eq_cubicHardProfileToRat]
  unfold cubicHardExpansion
  rw [Multiset.map_map]
  let pairEquivalence :
      (Fin termCount × CubicHardLatentLabeling) ≃
        (candidates × CubicHardLatentLabeling) :=
    Equiv.prodCongr enumeration (Equiv.refl _)
  let profileFunction :
      candidates × CubicHardLatentLabeling →
        (CubicHardJointScope → ℚ) :=
    fun expanded => cubicHardProfileToRat
      (cubicHardNatProfile
        (liftTuple
          (cubicHardCandidateTuple expanded.1.1) expanded.2))
  simpa only [pairEquivalence, profileFunction, Function.comp_apply]
    using univ_val_map_comp_equiv pairEquivalence profileFunction

structure CubicHardExpansionCollision where
  left : Finset CubicHardCandidate
  right : Finset CubicHardCandidate
  distinct : left ≠ right
  expansion_eq : cubicHardExpansion left = cubicHardExpansion right
  card_eq : left.card = right.card

/-- A fixed collision supplied by the finite pigeonhole theorem.  The target
distribution below does not depend on which collision is chosen. -/
noncomputable def cubicHardChosenCollision :
    CubicHardExpansionCollision :=
  { left := exists_cubicHardExpansion_collision.choose
    right := exists_cubicHardExpansion_collision.choose_spec.choose
    distinct := exists_cubicHardExpansion_collision.choose_spec.choose_spec.1
    expansion_eq :=
      exists_cubicHardExpansion_collision.choose_spec.choose_spec.2
    card_eq := cubicHardExpansion_collision_card_eq
      exists_cubicHardExpansion_collision.choose_spec.choose_spec.2 }

noncomputable abbrev cubicHardTermCount : Nat :=
  cubicHardChosenCollision.left.card

noncomputable def cubicHardPositiveEnumeration :
    Fin cubicHardTermCount ≃ cubicHardChosenCollision.left :=
  cubicHardChosenCollision.left.equivFin.symm

noncomputable def cubicHardNegativeEnumeration :
    Fin cubicHardTermCount ≃ cubicHardChosenCollision.right :=
  (finCongr cubicHardChosenCollision.card_eq).trans
    cubicHardChosenCollision.right.equivFin.symm

/-- The pigeonhole collision compiled into the boundary-safe marginal-trade
interface for cubic lifts with one hidden bit. -/
noncomputable def cubicHardOneHiddenCertificate :
    MarginalTradeCertificate 3 cubicHardDegree cubicHardTermCount
      (Fin 10) (Fin 1) where
  positive := fun term =>
    cubicHardCandidateTuple (cubicHardPositiveEnumeration term).1
  negative := fun term =>
    cubicHardCandidateTuple (cubicHardNegativeEnumeration term).1
  profileBalance := by
    rw [enumeratedProfileMultiset_eq_cubicHardExpansion
      cubicHardChosenCollision.left cubicHardPositiveEnumeration]
    rw [enumeratedProfileMultiset_eq_cubicHardExpansion
      cubicHardChosenCollision.right cubicHardNegativeEnumeration]
    rw [cubicHardChosenCollision.expansion_eq]

/-! ## The explicit full-support rational law -/

/-- Unnormalized rational cell weights.  They are pairwise powers of two,
with the distinguished filler cell assigned weight one. -/
def cubicHardUnnormalizedRat (visible : BitVec 10) : ℚ :=
  2 ^ cubicHardCellExponent visible

/-- The (finite, positive) rational normalizing constant. -/
noncomputable def cubicHardNormalizerRat : ℚ :=
  ∑ visible : BitVec 10, cubicHardUnnormalizedRat visible

theorem cubicHardUnnormalizedRat_pos (visible : BitVec 10) :
    0 < cubicHardUnnormalizedRat visible := by
  unfold cubicHardUnnormalizedRat
  exact pow_pos (by norm_num) _

theorem cubicHardNormalizerRat_pos : 0 < cubicHardNormalizerRat := by
  classical
  unfold cubicHardNormalizerRat
  exact Finset.sum_pos
    (fun visible _ => cubicHardUnnormalizedRat_pos visible)
    Finset.univ_nonempty

/-- Exact normalized rational weights of the target distribution. -/
noncomputable def cubicHardWeightsRat (visible : BitVec 10) : ℚ :=
  cubicHardUnnormalizedRat visible / cubicHardNormalizerRat

theorem cubicHardWeightsRat_pos (visible : BitVec 10) :
    0 < cubicHardWeightsRat visible := by
  exact div_pos (cubicHardUnnormalizedRat_pos visible)
    cubicHardNormalizerRat_pos

theorem sum_cubicHardWeightsRat :
    (∑ visible : BitVec 10, cubicHardWeightsRat visible) = 1 := by
  classical
  unfold cubicHardWeightsRat cubicHardNormalizerRat
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos
    (fun visible _ => cubicHardUnnormalizedRat_pos visible)
    Finset.univ_nonempty))

/-- Real coercion of the exact rational probability table. -/
noncomputable def cubicHardWeights (visible : BitVec 10) : ℝ :=
  cubicHardWeightsRat visible

/-- The explicit target law on ten visible bits. -/
noncomputable def cubicHardDistribution : Distribution (BitVec 10) :=
  distributionOfRealWeights cubicHardWeights
    (fun visible => Rat.cast_nonneg.mpr
      (cubicHardWeightsRat_pos visible).le)
    (by
      have hCast := congrArg (fun value : ℚ => (value : ℝ))
        sum_cubicHardWeightsRat
      simpa [cubicHardWeights, Rat.cast_sum] using hCast)

@[simp]
theorem cubicHardDistribution_apply_toReal (visible : BitVec 10) :
    (cubicHardDistribution visible).toReal = cubicHardWeights visible := by
  exact distributionOfRealWeights_apply_toReal _ _ _ visible

/-- The lower bound is genuinely weight-sensitive: every visible string has
strictly positive rational mass. -/
theorem cubicHardDistribution_support :
    cubicHardDistribution.support = Set.univ := by
  ext visible
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff cubicHardDistribution visible).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [cubicHardDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  have hPositive : 0 < cubicHardWeights visible :=
    Rat.cast_pos.mpr (cubicHardWeightsRat_pos visible)
  exact (ne_of_gt hPositive) hReal

/-! ## Detection by uniqueness of binary expansion -/

/-- The unnormalized monomial attached to a candidate is its binary code
power. -/
theorem prod_cubicHardUnnormalizedRat_candidateTuple
    (candidate : CubicHardCandidate) :
    (∏ index : Fin cubicHardDegree,
      cubicHardUnnormalizedRat
        (cubicHardCandidateTuple candidate index)) =
      (2 : ℚ) ^ cubicHardCandidateCode candidate := by
  unfold cubicHardUnnormalizedRat
  rw [Finset.prod_pow_eq_pow_sum]
  rw [sum_cubicHardCellExponent_candidateTuple]

/-- Normalizing a candidate monomial contributes the same denominator to
every candidate, because all tuples have common degree. -/
theorem prod_cubicHardWeightsRat_candidateTuple
    (candidate : CubicHardCandidate) :
    (∏ index : Fin cubicHardDegree,
      cubicHardWeightsRat (cubicHardCandidateTuple candidate index)) =
      (2 : ℚ) ^ cubicHardCandidateCode candidate /
        cubicHardNormalizerRat ^ cubicHardDegree := by
  unfold cubicHardWeightsRat
  rw [Finset.prod_div_distrib]
  rw [prod_cubicHardUnnormalizedRat_candidateTuple]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Binary sum encoding of a finite candidate family. -/
def cubicHardCandidatePowerSum
    (candidates : Finset CubicHardCandidate) : Nat :=
  ∑ candidate ∈ candidates, 2 ^ cubicHardCandidateCode candidate

/-- Distinct candidate families have distinct sums of their code powers.
This is the computational link from the abstract profile collision to the
explicit target weights. -/
theorem cubicHardCandidatePowerSum_injective :
    Function.Injective cubicHardCandidatePowerSum := by
  classical
  intro left right hSums
  apply Finset.image_injective cubicHardCandidateCode_injective
  apply Finset.geomSum_injective (n := 2) (by omega)
  have hLeft :
      (∑ code ∈ left.image cubicHardCandidateCode, 2 ^ code) =
        cubicHardCandidatePowerSum left := by
    rw [Finset.sum_image cubicHardCandidateCode_injective.injOn]
    rfl
  have hRight :
      (∑ code ∈ right.image cubicHardCandidateCode, 2 ^ code) =
        cubicHardCandidatePowerSum right := by
    rw [Finset.sum_image cubicHardCandidateCode_injective.injOn]
    rfl
  change
    (∑ code ∈ left.image cubicHardCandidateCode, 2 ^ code) =
      ∑ code ∈ right.image cubicHardCandidateCode, 2 ^ code
  exact hLeft.trans (hSums.trans hRight.symm)

/-- Evaluate any enumerated candidate family on the real target table. -/
theorem sum_prod_cubicHardWeights_of_equiv
    {termCount : Nat}
    (candidates : Finset CubicHardCandidate)
    (enumeration : Fin termCount ≃ candidates) :
    (∑ term : Fin termCount,
      ∏ index : Fin cubicHardDegree,
        cubicHardWeights
          (cubicHardCandidateTuple (enumeration term).1 index)) =
      (cubicHardCandidatePowerSum candidates : ℝ) /
        (cubicHardNormalizerRat : ℝ) ^ cubicHardDegree := by
  classical
  calc
    (∑ term : Fin termCount,
        ∏ index : Fin cubicHardDegree,
          cubicHardWeights
            (cubicHardCandidateTuple (enumeration term).1 index)) =
        ∑ candidate : candidates,
          ∏ index : Fin cubicHardDegree,
            cubicHardWeights
              (cubicHardCandidateTuple candidate.1 index) := by
      exact enumeration.sum_comp (fun candidate : candidates =>
        ∏ index : Fin cubicHardDegree,
          cubicHardWeights
            (cubicHardCandidateTuple candidate.1 index))
    _ = (cubicHardCandidatePowerSum candidates : ℝ) /
          (cubicHardNormalizerRat : ℝ) ^ cubicHardDegree := by
      rw [show
        (∑ candidate : candidates,
          ∏ index : Fin cubicHardDegree,
            cubicHardWeights
              (cubicHardCandidateTuple candidate.1 index)) =
        ∑ candidate ∈ candidates,
          ∏ index : Fin cubicHardDegree,
            cubicHardWeights
              (cubicHardCandidateTuple candidate index) from
        Finset.sum_coe_sort candidates (fun candidate =>
          ∏ index : Fin cubicHardDegree,
            cubicHardWeights
              (cubicHardCandidateTuple candidate index))]
      simp_rw [cubicHardWeights]
      simp_rw [← Rat.cast_prod]
      simp_rw [prod_cubicHardWeightsRat_candidateTuple]
      simp_rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
      rw [← Finset.sum_div]
      congr 1
      norm_cast

theorem cubicHardOneHidden_positiveValue :
    cubicHardOneHiddenCertificate.positiveValue cubicHardWeights =
      (cubicHardCandidatePowerSum
          cubicHardChosenCollision.left : ℝ) /
        (cubicHardNormalizerRat : ℝ) ^ cubicHardDegree := by
  simpa [MarginalTradeCertificate.positiveValue,
    cubicHardOneHiddenCertificate] using
    sum_prod_cubicHardWeights_of_equiv cubicHardChosenCollision.left
      cubicHardPositiveEnumeration

theorem cubicHardOneHidden_negativeValue :
    cubicHardOneHiddenCertificate.negativeValue cubicHardWeights =
      (cubicHardCandidatePowerSum
          cubicHardChosenCollision.right : ℝ) /
        (cubicHardNormalizerRat : ℝ) ^ cubicHardDegree := by
  simpa [MarginalTradeCertificate.negativeValue,
    cubicHardOneHiddenCertificate] using
    sum_prod_cubicHardWeights_of_equiv cubicHardChosenCollision.right
      cubicHardNegativeEnumeration

/-- The chosen marginal trade is nonzero on the explicit target. -/
theorem cubicHardOneHidden_detects :
    cubicHardOneHiddenCertificate.positiveValue
        (fun visible => (cubicHardDistribution visible).toReal) ≠
      cubicHardOneHiddenCertificate.negativeValue
        (fun visible => (cubicHardDistribution visible).toReal) := by
  simp_rw [cubicHardDistribution_apply_toReal]
  rw [cubicHardOneHidden_positiveValue,
    cubicHardOneHidden_negativeValue]
  intro hEqual
  have hDenominator :
      (cubicHardNormalizerRat : ℝ) ^ cubicHardDegree ≠ 0 :=
    pow_ne_zero _ (Rat.cast_ne_zero.mpr
      (ne_of_gt cubicHardNormalizerRat_pos))
  have hNumerators :
      (cubicHardCandidatePowerSum cubicHardChosenCollision.left : ℝ) =
        (cubicHardCandidatePowerSum cubicHardChosenCollision.right : ℝ) :=
    (div_left_inj' hDenominator).mp hEqual
  have hNat :
      cubicHardCandidatePowerSum cubicHardChosenCollision.left =
        cubicHardCandidatePowerSum cubicHardChosenCollision.right := by
    exact_mod_cast hNumerators
  exact cubicHardChosenCollision.distinct
    (cubicHardCandidatePowerSum_injective hNat)

/-- In particular, no cubic localization of the target can use one hidden
bit. -/
theorem cubicHardDistribution_no_oneHidden :
    ¬HasKLocalizationBits 3 1 10 cubicHardDistribution :=
  cubicHardOneHiddenCertificate.obstructs_localization
    cubicHardOneHidden_detects

/-! ## The zero-hidden obstruction -/

/-- Low and high coordinate projections for the decomposition `10 = 4 + 6`. -/
def cubicHardLowPart (visible : BitVec 10) : BitVec 4 :=
  fun coordinate => visible (Fin.castAdd 6 coordinate)

def cubicHardHighPart (visible : BitVec 10) : BitVec 6 :=
  fun coordinate => visible (Fin.natAdd 4 coordinate)

/-- Alternating direction on the four-dimensional face where the last six
bits vanish (equivalently, the first sixteen little-endian binary states). -/
def cubicHardLowFaceDirectionRat (visible : BitVec 10) : ℚ :=
  if cubicHardHighPart visible = allFalseBitVec 6 then
    evenParityDirectionRat 4 (cubicHardLowPart visible)
  else 0

@[simp]
theorem cubicHardLowPart_flipBit
    (coordinate : Fin 4) (visible : BitVec 10) :
    cubicHardLowPart (flipBit (Fin.castAdd 6 coordinate) visible) =
      flipBit coordinate (cubicHardLowPart visible) := by
  funext candidate
  by_cases hSame : candidate = coordinate
  · subst candidate
    simp [cubicHardLowPart, flipBit]
  · have hCast : Fin.castAdd 6 candidate ≠ Fin.castAdd 6 coordinate :=
      fun hEqual => hSame (Fin.castAdd_injective 4 6 hEqual)
    simp [cubicHardLowPart, flipBit, hSame, hCast]

@[simp]
theorem cubicHardHighPart_flipBit
    (coordinate : Fin 4) (visible : BitVec 10) :
    cubicHardHighPart (flipBit (Fin.castAdd 6 coordinate) visible) =
      cubicHardHighPart visible := by
  funext candidate
  rw [cubicHardHighPart, cubicHardHighPart]
  apply flipBit_apply_of_ne
  intro hEqual
  have hValues := congrArg Fin.val hEqual
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hValues
  omega

theorem cubicHardLowFaceDirectionRat_flipBit
    (coordinate : Fin 4) (visible : BitVec 10) :
    cubicHardLowFaceDirectionRat
        (flipBit (Fin.castAdd 6 coordinate) visible) =
      -cubicHardLowFaceDirectionRat visible := by
  unfold cubicHardLowFaceDirectionRat
  rw [cubicHardLowPart_flipBit, cubicHardHighPart_flipBit]
  by_cases hHigh : cubicHardHighPart visible = allFalseBitVec 6
  · simp only [hHigh, if_true]
    exact evenParityDirectionRat_flipBit coordinate
      (cubicHardLowPart visible)
  · simp [hHigh]

theorem exists_cubicHardLowCoordinate_not_mem
    (scope : FeatureScope (Fin 10) 3) :
    ∃ coordinate : Fin 4, Fin.castAdd 6 coordinate ∉ scope.1 := by
  classical
  by_contra hNone
  push_neg at hNone
  let embedding : Fin 4 ↪ Fin 10 :=
    ⟨Fin.castAdd 6, Fin.castAdd_injective 4 6⟩
  have hSubset :
      (Finset.univ : Finset (Fin 4)).map embedding ⊆ scope.1 := by
    intro value hValue
    rcases Finset.mem_map.mp hValue with ⟨coordinate, _, rfl⟩
    exact hNone coordinate
  have hCard := Finset.card_le_card hSubset
  have hEmbeddedCard :
      ((Finset.univ : Finset (Fin 4)).map embedding).card = 4 := by
    simp [embedding]
  rw [hEmbeddedCard] at hCard
  omega

/-- The four-face alternating direction annihilates every cubic visible
feature. -/
theorem cubicHardLowFaceDirectionRat_momentBalance :
    ∀ scope : FeatureScope (Fin 10) 3,
      ∑ visible : BitVec 10,
        cubicHardLowFaceDirectionRat visible *
          rationalMonomialValue scope.1 visible = 0 := by
  intro scope
  classical
  rcases exists_cubicHardLowCoordinate_not_mem scope with
    ⟨coordinate, hUnused⟩
  let summand : BitVec 10 → ℚ := fun visible =>
    cubicHardLowFaceDirectionRat visible *
      rationalMonomialValue scope.1 visible
  have hSummandFlip : ∀ visible : BitVec 10,
      summand (flipBit (Fin.castAdd 6 coordinate) visible) =
        -summand visible := by
    intro visible
    simp only [summand, cubicHardLowFaceDirectionRat_flipBit]
    rw [rationalMonomialValue_flipBit_of_not_mem
      scope.1 visible (Fin.castAdd 6 coordinate) hUnused]
    ring
  have hReindex :=
    (flipBitEquiv (Fin.castAdd 6 coordinate)).sum_comp summand
  have hNeg : (∑ visible : BitVec 10, summand visible) =
      -(∑ visible : BitVec 10, summand visible) := by
    calc
      (∑ visible : BitVec 10, summand visible) =
          ∑ visible : BitVec 10,
            summand (flipBit (Fin.castAdd 6 coordinate) visible) :=
        hReindex.symm
      _ = ∑ visible : BitVec 10, -summand visible := by
        apply Finset.sum_congr rfl
        intro visible _
        exact hSummandFlip visible
      _ = -(∑ visible : BitVec 10, summand visible) := by
        rw [Finset.sum_neg_distrib]
  linarith

theorem sum_cubicHardLowFaceDirectionRat :
    (∑ visible : BitVec 10, cubicHardLowFaceDirectionRat visible) = 0 := by
  let empty : FeatureScope (Fin 10) 3 := ⟨∅, by simp⟩
  have hBalance := cubicHardLowFaceDirectionRat_momentBalance empty
  simpa [rationalMonomialValue] using hBalance

@[simp]
theorem cubicHardLowPart_append
    (low : BitVec 4) (high : BitVec 6) :
    cubicHardLowPart (Fin.append low high) = low := by
  funext coordinate
  simp [cubicHardLowPart]

@[simp]
theorem cubicHardHighPart_append
    (low : BitVec 4) (high : BitVec 6) :
    cubicHardHighPart (Fin.append low high) = high := by
  funext coordinate
  simp [cubicHardHighPart]

@[simp]
theorem cubicHardLowFaceDirectionRat_append
    (low : BitVec 4) (high : BitVec 6) :
    cubicHardLowFaceDirectionRat (Fin.append low high) =
      if high = allFalseBitVec 6 then
        evenParityDirectionRat 4 low else 0 := by
  simp [cubicHardLowFaceDirectionRat]

theorem binaryAssignmentValue_append_allFalse
    (low : BitVec 4) :
    binaryAssignmentValue (Fin.append low (allFalseBitVec 6)) =
      binaryAssignmentValue low := by
  unfold binaryAssignmentValue
  rw [Fin.sum_univ_add]
  simp [allFalseBitVec]

theorem cubicHardAppend_allFalse_ne_filler
    (low : BitVec 4) :
    Fin.append low (allFalseBitVec 6) ≠ cubicHardFillerState := by
  intro hEqual
  have hValues := congrArg binaryAssignmentValue hEqual
  rw [binaryAssignmentValue_append_allFalse] at hValues
  rw [cubicHardFillerState,
    binaryAssignmentValue_binaryAssignment_of_lt
      (ell := 10) (value := 1023) (by norm_num)] at hValues
  have hLow := binaryAssignmentValue_lt_two_pow low
  norm_num at hLow
  omega

@[simp]
theorem cubicHardCellExponent_append_allFalse
    (low : BitVec 4) :
    cubicHardCellExponent (Fin.append low (allFalseBitVec 6)) =
      cubicHardDigitBase ^ binaryAssignmentValue low := by
  rw [cubicHardCellExponent,
    if_neg (cubicHardAppend_allFalse_ne_filler low)]
  rw [binaryAssignmentValue_append_allFalse]

/-- Coordinate enumeration used only to reduce a sixteen-term rational sum
inside the kernel. -/
def cubicHardBitVecFourEquiv :
    BitVec 4 ≃ Bool × Bool × Bool × Bool where
  toFun assignment :=
    (assignment 0, assignment 1, assignment 2, assignment 3)
  invFun bits := ![bits.1, bits.2.1, bits.2.2.1, bits.2.2.2]
  left_inv assignment := by
    funext coordinate
    fin_cases coordinate <;> rfl
  right_inv bits := by
    rcases bits with ⟨first, second, third, fourth⟩
    rfl

theorem cubicHardSmallExponentPairing_ne_zero :
    (∑ low : BitVec 4,
      evenParityDirectionRat 4 low *
        (cubicHardDigitBase ^ binaryAssignmentValue low : ℚ)) ≠ 0 := by
  rw [← cubicHardBitVecFourEquiv.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  norm_num [cubicHardBitVecFourEquiv, evenParityDirectionRat,
    parityCoordinateSign, binaryAssignmentValue, cubicHardDigitBase,
    Fin.prod_univ_succ, Fin.sum_univ_succ]

/-- The same direction does not annihilate the exponent table defining the
target weights. -/
theorem cubicHardLowFace_exponentPairing_ne_zero :
    (∑ visible : BitVec 10,
      cubicHardLowFaceDirectionRat visible *
        (cubicHardCellExponent visible : ℚ)) ≠ 0 := by
  classical
  rw [← (Fin.appendEquiv 4 6).sum_comp]
  rw [Fintype.sum_prod_type]
  change
    (∑ low : BitVec 4, ∑ high : BitVec 6,
      cubicHardLowFaceDirectionRat (Fin.append low high) *
        (cubicHardCellExponent (Fin.append low high) : ℚ)) ≠ 0
  have hReduce :
      (∑ low : BitVec 4, ∑ high : BitVec 6,
        cubicHardLowFaceDirectionRat (Fin.append low high) *
          (cubicHardCellExponent (Fin.append low high) : ℚ)) =
        ∑ low : BitVec 4,
          evenParityDirectionRat 4 low *
            (cubicHardCellExponent
              (Fin.append low (allFalseBitVec 6)) : ℚ) := by
    apply Finset.sum_congr rfl
    intro low _
    rw [Fintype.sum_eq_single (allFalseBitVec 6)]
    · simp
    · intro high hNe
      simp [hNe]
  rw [hReduce]
  simp_rw [cubicHardCellExponent_append_allFalse]
  exact cubicHardSmallExponentPairing_ne_zero

theorem cubicHard_log_weights_formula (visible : BitVec 10) :
    Real.log (cubicHardWeights visible) =
      (cubicHardCellExponent visible : ℝ) * Real.log 2 -
        Real.log (cubicHardNormalizerRat : ℝ) := by
  unfold cubicHardWeights cubicHardWeightsRat cubicHardUnnormalizedRat
  rw [Rat.cast_div, Rat.cast_pow]
  norm_num only [Rat.cast_ofNat]
  rw [Real.log_div
    (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
    (Rat.cast_ne_zero.mpr (ne_of_gt cubicHardNormalizerRat_pos))]
  rw [Real.log_pow]

/-- The low-face direction detects a nonzero four-way interaction in the
log-density of the explicit target. -/
theorem cubicHardLowFace_alternatingLogSum_ne_zero :
    (∑ visible : BitVec 10,
      (cubicHardLowFaceDirectionRat visible : ℝ) *
        Real.log (cubicHardWeights visible)) ≠ 0 := by
  classical
  have hDirectionCast := congrArg (fun value : ℚ => (value : ℝ))
    sum_cubicHardLowFaceDirectionRat
  have hDirectionSum :
      (∑ visible : BitVec 10,
        (cubicHardLowFaceDirectionRat visible : ℝ)) = 0 := by
    simpa [Rat.cast_sum] using hDirectionCast
  let exponentPairing : ℚ := ∑ visible : BitVec 10,
    cubicHardLowFaceDirectionRat visible *
      (cubicHardCellExponent visible : ℚ)
  have hPairingNe : exponentPairing ≠ 0 := by
    exact cubicHardLowFace_exponentPairing_ne_zero
  have hPairingCast :
      (∑ visible : BitVec 10,
        (cubicHardLowFaceDirectionRat visible : ℝ) *
          (cubicHardCellExponent visible : ℝ)) =
        (exponentPairing : ℝ) := by
    unfold exponentPairing
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]
  have hExponentTerm :
      (∑ visible : BitVec 10,
        (cubicHardLowFaceDirectionRat visible : ℝ) *
          ((cubicHardCellExponent visible : ℝ) * Real.log 2)) =
        (exponentPairing : ℝ) * Real.log 2 := by
    calc
      _ = (∑ visible : BitVec 10,
          (cubicHardLowFaceDirectionRat visible : ℝ) *
            (cubicHardCellExponent visible : ℝ)) * Real.log 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro visible _
        ring
      _ = _ := by rw [hPairingCast]
  have hConstantTerm :
      (∑ visible : BitVec 10,
        (cubicHardLowFaceDirectionRat visible : ℝ) *
          Real.log (cubicHardNormalizerRat : ℝ)) = 0 := by
    calc
      _ = (∑ visible : BitVec 10,
          (cubicHardLowFaceDirectionRat visible : ℝ)) *
            Real.log (cubicHardNormalizerRat : ℝ) := by
        rw [Finset.sum_mul]
      _ = 0 := by rw [hDirectionSum, zero_mul]
  simp_rw [cubicHard_log_weights_formula, mul_sub]
  rw [Finset.sum_sub_distrib, hExponentTerm, hConstantTerm, sub_zero]
  exact mul_ne_zero (Rat.cast_ne_zero.mpr hPairingNe)
    (ne_of_gt (Real.log_pos (by norm_num)))

/-- Rational log-interaction certificate ruling out a zero-hidden cubic
localization of the same target. -/
noncomputable def cubicHardZeroHiddenLogCertificate :
    RationalLogInteractionCertificate 3 cubicHardDistribution where
  direction := cubicHardLowFaceDirectionRat
  momentBalance := cubicHardLowFaceDirectionRat_momentBalance
  detectsLogDensity := by
    simp_rw [cubicHardDistribution_apply_toReal]
    exact cubicHardLowFace_alternatingLogSum_ne_zero

theorem cubicHardDistribution_not_threeLocal :
    ¬IsKLocalMarginal 3 cubicHardDistribution :=
  cubicHardZeroHiddenLogCertificate.not_isKLocalMarginal
    cubicHardDistribution_support

theorem cubicHardDistribution_no_zeroHidden :
    ¬HasKLocalizationBits 3 0 10 cubicHardDistribution := by
  intro hLocalization
  exact cubicHardDistribution_not_threeLocal
    ((hasKLocalization_zero_iff_isKLocalMarginal
      3 cubicHardDistribution).1 hLocalization)

/-- Main result: this concrete full-support rational law needs at least two
hidden bits in every cubic localization. -/
theorem cubicHardDistribution_localizationComplexity_gt_one :
    1 < localizationComplexityBits 3 10 cubicHardDistribution := by
  have hExists := kLocalization_exists cubicHardDistribution
    (by omega : 2 ≤ 3)
  have hOptimal := localizationComplexityBits_spec
    3 10 cubicHardDistribution hExists
  by_contra hNotGreater
  have hAtMost :
      localizationComplexityBits 3 10 cubicHardDistribution ≤ 1 :=
    Nat.le_of_not_gt hNotGreater
  have hCases :
      localizationComplexityBits 3 10 cubicHardDistribution = 0 ∨
        localizationComplexityBits 3 10 cubicHardDistribution = 1 := by
    omega
  rcases hCases with hZero | hOne
  · rw [hZero] at hOptimal
    exact cubicHardDistribution_no_zeroHidden hOptimal
  · rw [hOne] at hOptimal
    exact cubicHardDistribution_no_oneHidden hOptimal

end KLocality
