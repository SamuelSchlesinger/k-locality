import KLocality.BlockParityFiber
import KLocality.MarginalTradeCertificate
import KLocality.UniformParityUpperBound

namespace KLocality

open scoped BigOperators

/-!
# The structured block-parity profile matrix

This file gives numerical, executable indices to the block-parity family.
For prefix width `q` there are `N = 2^q` blocks, `2^N` candidate truth
tables, and every candidate monomial has degree `8N`.  A candidate is encoded
by the little-endian integer represented by its truth table.
-/

def blockParityPrefixCount (q : Nat) : Nat := 2 ^ q

def blockParityDegree (q : Nat) : Nat := blockParityPrefixCount q * 8

def blockParityCandidateCount (q : Nat) : Nat :=
  2 ^ blockParityPrefixCount q

abbrev BlockParityCandidateCode (q : Nat) :=
  Fin (blockParityCandidateCount q)

/-- Decode the numerical candidate index as a truth table on `q` bits. -/
def blockParityTruthTable
    {q : Nat} (candidate : BlockParityCandidateCode q)
    (label : BitVec q) : Bool :=
  binaryAssignment (blockParityPrefixCount q) candidate.val
    ⟨binaryAssignmentValue label, by
      simpa [blockParityPrefixCount] using
        binaryAssignmentValue_lt_two_pow label⟩

/-- Encode a truth table as its little-endian binary integer. -/
def blockParityTruthTableCode
    {q : Nat} (test : BitVec q -> Bool) : BlockParityCandidateCode q :=
  ⟨binaryAssignmentValue
      (fun block : Fin (blockParityPrefixCount q) =>
        test (binaryAssignment q block.val)), by
    simpa [blockParityCandidateCount, blockParityPrefixCount] using
      binaryAssignmentValue_lt_two_pow
        (fun block : Fin (blockParityPrefixCount q) =>
          test (binaryAssignment q block.val))⟩

@[simp]
theorem blockParityTruthTable_binaryAssignment
    {q : Nat} (candidate : BlockParityCandidateCode q)
    (block : Fin (blockParityPrefixCount q)) :
    blockParityTruthTable candidate (binaryAssignment q block.val) =
      binaryAssignment (blockParityPrefixCount q) candidate.val block := by
  simp only [blockParityTruthTable]
  congr 1
  apply Fin.ext
  exact binaryAssignmentValue_binaryAssignment_of_lt block.isLt

theorem binaryAssignment_binaryAssignmentValue
    {q : Nat} (label : BitVec q) :
    binaryAssignment q (binaryAssignmentValue label) = label := by
  apply binaryAssignmentValue_injective q
  rw [binaryAssignmentValue_binaryAssignment_of_lt
    (binaryAssignmentValue_lt_two_pow label)]

@[simp]
theorem blockParityTruthTableCode_truthTable
    {q : Nat} (candidate : BlockParityCandidateCode q) :
    blockParityTruthTableCode (blockParityTruthTable candidate) = candidate := by
  apply Fin.ext
  simp only [blockParityTruthTableCode]
  have hAssignments :
      (fun block : Fin (blockParityPrefixCount q) =>
        blockParityTruthTable candidate (binaryAssignment q block.val)) =
      binaryAssignment (blockParityPrefixCount q) candidate.val := by
    funext block
    exact blockParityTruthTable_binaryAssignment candidate block
  rw [hAssignments, binaryAssignmentValue_binaryAssignment_of_lt candidate.isLt]

@[simp]
theorem blockParityTruthTable_code
    {q : Nat} (test : BitVec q -> Bool) :
    blockParityTruthTable (blockParityTruthTableCode test) = test := by
  funext label
  let block : Fin (blockParityPrefixCount q) :=
    ⟨binaryAssignmentValue label, by
      simpa [blockParityPrefixCount] using
        binaryAssignmentValue_lt_two_pow label⟩
  have hLabel : binaryAssignment q block.val = label := by
    exact binaryAssignment_binaryAssignmentValue label
  rw [← hLabel, blockParityTruthTable_binaryAssignment]
  let encoded : Assignment (Fin (blockParityPrefixCount q)) :=
    fun block => test (binaryAssignment q block.val)
  have hDecoded :
      binaryAssignment (blockParityPrefixCount q)
          (binaryAssignmentValue encoded) = encoded :=
    binaryAssignment_binaryAssignmentValue encoded
  change binaryAssignment (blockParityPrefixCount q)
      (binaryAssignmentValue encoded) block = encoded block
  exact congrFun hDecoded block

/-- Numerical candidate codes are exactly Boolean truth tables on `q` bits. -/
def blockParityCandidateEquiv (q : Nat) :
    BlockParityCandidateCode q ≃ (BitVec q -> Bool) where
  toFun := blockParityTruthTable
  invFun := blockParityTruthTableCode
  left_inv := blockParityTruthTableCode_truthTable
  right_inv := blockParityTruthTable_code

@[simp]
theorem blockParityCandidateEquiv_apply
    (q : Nat) (candidate : BlockParityCandidateCode q) :
    blockParityCandidateEquiv q candidate =
      blockParityTruthTable candidate :=
  rfl

/-! ## An explicit enumeration of each parity half -/

/-- Complete three low bits to four bits with the requested parity. -/
def parityCompletion (target : Bool) (low : BitVec 3) : BitVec 4 :=
  fun coordinate =>
    if hLow : coordinate.val < 3 then low ⟨coordinate.val, hLow⟩
    else xor (xor (low 0) (low 1)) (xor (low 2) target)

theorem parityFour_parityCompletion :
    ∀ (target : Bool) (low : BitVec 3),
      parityFour (parityCompletion target low) = target := by
  decide

theorem parityCompletion_injective (target : Bool) :
    Function.Injective (parityCompletion target) := by
  intro left right hEqual
  funext coordinate
  have hCoordinate := congrFun hEqual coordinate.castSucc
  simpa [parityCompletion] using hCoordinate

/-- Split a tuple position into a prefix block and one of eight points in the
selected parity half. -/
def blockParityIndexEquiv (q : Nat) :
    Fin (blockParityPrefixCount q) × Fin 8 ≃ Fin (blockParityDegree q) :=
  finProdFinEquiv

/-- The degree-`8*2^q` visible tuple belonging to one encoded truth table. -/
def blockParityCandidateTuple
    (q : Nat) (candidate : BlockParityCandidateCode q) :
    Fin (blockParityDegree q) -> Assignment (BlockParityVar q) :=
  fun index =>
    let blockSlot := (blockParityIndexEquiv q).symm index
    let label := binaryAssignment q blockSlot.1.val
    let low := binaryAssignment 3 blockSlot.2.val
    blockParityState label
      (parityCompletion (blockParityTruthTable candidate label) low)

@[simp]
theorem blockParityCandidateTuple_index
    (q : Nat) (candidate : BlockParityCandidateCode q)
    (block : Fin (blockParityPrefixCount q)) (slot : Fin 8) :
    blockParityCandidateTuple q candidate
        (blockParityIndexEquiv q (block, slot)) =
      blockParityState (binaryAssignment q block.val)
        (parityCompletion
          (blockParityTruthTable candidate
            (binaryAssignment q block.val))
          (binaryAssignment 3 slot.val)) := by
  simp [blockParityCandidateTuple]

/-! ## Exact expanded cubic profiles -/

abbrev BlockParityJointScope (q latentBits : Nat) :=
  FeatureScope (Sum (BlockParityVar q) (Fin latentBits)) 3

/-- Natural-valued cubic profile of one lifted block-parity tuple. -/
def blockParityNatProfile
    (q latentBits : Nat)
    (tuple : Fin (blockParityDegree q) ->
      Assignment (Sum (BlockParityVar q) (Fin latentBits))) :
    BlockParityJointScope q latentBits -> Fin (blockParityDegree q + 1) :=
  fun scope =>
    ⟨((Finset.univ : Finset (Fin (blockParityDegree q))).filter
      fun index => scope.1 ⊆ trueCoordinates (tuple index)).card,
      Nat.lt_succ_of_le (by
        have hCard := Finset.card_filter_le
          (Finset.univ : Finset (Fin (blockParityDegree q)))
          (fun index => scope.1 ⊆ trueCoordinates (tuple index))
        simpa only [Finset.card_univ, Fintype.card_fin] using hCard)⟩

abbrev BlockParityNatProfile (q latentBits : Nat) :=
  BlockParityJointScope q latentBits -> Fin (blockParityDegree q + 1)

/-- Interpret a numerical profile as the rational profile used by the
boundary-safe marginal-trade API. -/
def blockParityProfileToRat
    {q latentBits : Nat}
    (profile : BlockParityNatProfile q latentBits) :
    BlockParityJointScope q latentBits -> ℚ :=
  fun scope => profile scope

theorem tupleFeatureProfile_eq_blockParityProfileToRat
    (q latentBits : Nat)
    (tuple : Fin (blockParityDegree q) ->
      Assignment (Sum (BlockParityVar q) (Fin latentBits))) :
    tupleFeatureProfile 3 (blockParityDegree q) tuple =
      blockParityProfileToRat (blockParityNatProfile q latentBits tuple) := by
  funext scope
  let predicate : Fin (blockParityDegree q) -> Prop := fun index =>
    scope.1 ⊆ trueCoordinates (tuple index)
  have hCard := Finset.card_filter predicate
    (Finset.univ : Finset (Fin (blockParityDegree q)))
  have hCast := congrArg (fun value : Nat => (value : ℚ)) hCard
  simpa only [tupleFeatureProfile, blockParityProfileToRat,
    blockParityNatProfile, rationalMonomialValue, predicate,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_const_zero, Finset.sum_filter] using hCast.symm

abbrev BlockParityLatentLabeling (q latentBits : Nat) :=
  Fin (blockParityDegree q) -> Assignment (Fin latentBits)

theorem blockParityLatentLabeling_card (q latentBits : Nat) :
    Fintype.card (BlockParityLatentLabeling q latentBits) =
      2 ^ (latentBits * blockParityDegree q) := by
  simp only [BlockParityLatentLabeling, Assignment, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  exact (pow_mul 2 latentBits (blockParityDegree q)).symm

/-- Multiset of all joint cubic profiles obtained by assigning latent labels
to every factor of one visible candidate tuple.  This is one column of
`M_(q,L)`. -/
def blockParityColumn
    (q latentBits : Nat) (candidate : BlockParityCandidateCode q) :
    Multiset (BlockParityNatProfile q latentBits) :=
  ((Finset.univ : Finset
      (BlockParityLatentLabeling q latentBits))).val.map
    (fun latent =>
      blockParityNatProfile q latentBits
        (liftTuple (blockParityCandidateTuple q candidate) latent))

theorem blockParityColumn_card
    (q latentBits : Nat) (candidate : BlockParityCandidateCode q) :
    (blockParityColumn q latentBits candidate).card =
      2 ^ (latentBits * blockParityDegree q) := by
  simp only [blockParityColumn, Multiset.card_map, Finset.card_val,
    Finset.card_univ, BlockParityLatentLabeling, Assignment,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact (pow_mul 2 latentBits (blockParityDegree q)).symm

/-- Decode a numerical subset of the candidate columns. -/
def blockParitySubsetContains
    {q : Nat}
    (subset : Fin (2 ^ blockParityCandidateCount q))
    (candidate : BlockParityCandidateCode q) : Bool :=
  binaryAssignment (blockParityCandidateCount q) subset.val candidate

/-- Sum of selected matrix columns at one profile row. -/
def blockParitySubsetProfileCount
    (q latentBits : Nat)
    (subset : Fin (2 ^ blockParityCandidateCount q))
    (profile : BlockParityNatProfile q latentBits) : Nat :=
  ∑ candidate : BlockParityCandidateCode q,
    if blockParitySubsetContains subset candidate then
      (blockParityColumn q latentBits candidate).count profile
    else 0

def blockParityHistogramCoordinateBound (q latentBits : Nat) : Nat :=
  blockParityCandidateCount q *
      2 ^ (latentBits * blockParityDegree q) + 1

theorem blockParitySubsetProfileCount_lt
    (q latentBits : Nat)
    (subset : Fin (2 ^ blockParityCandidateCount q))
    (profile : BlockParityNatProfile q latentBits) :
    blockParitySubsetProfileCount q latentBits subset profile <
      blockParityHistogramCoordinateBound q latentBits := by
  classical
  calc
    blockParitySubsetProfileCount q latentBits subset profile ≤
        ∑ _candidate : BlockParityCandidateCode q,
          2 ^ (latentBits * blockParityDegree q) := by
      unfold blockParitySubsetProfileCount
      apply Finset.sum_le_sum
      intro candidate _
      split
      · exact (Multiset.count_le_card profile
          (blockParityColumn q latentBits candidate)).trans_eq
            (blockParityColumn_card q latentBits candidate)
      · exact Nat.zero_le _
    _ = blockParityCandidateCount q *
        2 ^ (latentBits * blockParityDegree q) := by
      simp [blockParityCandidateCount]
    _ < blockParityHistogramCoordinateBound q latentBits := by
      unfold blockParityHistogramCoordinateBound
      omega

abbrev BlockParityHistogram (q latentBits : Nat) :=
  BlockParityNatProfile q latentBits ->
    Fin (blockParityHistogramCoordinateBound q latentBits)

/-- The complete aggregate profile histogram of an encoded subset of
columns. -/
def blockParitySubsetHistogram
    (q latentBits : Nat)
    (subset : Fin (2 ^ blockParityCandidateCount q)) :
    BlockParityHistogram q latentBits :=
  fun profile =>
    ⟨blockParitySubsetProfileCount q latentBits subset profile,
      blockParitySubsetProfileCount_lt q latentBits subset profile⟩

end KLocality
