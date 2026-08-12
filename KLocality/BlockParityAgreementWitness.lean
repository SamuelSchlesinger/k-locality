import KLocality.BlockParityCanonicalTrade
import KLocality.BinaryAgreementTransform

namespace KLocality

open scoped BigOperators

/-!
# Canonical detection by the 256-agreement tensor

The signed collision trade is nonzero.  The tensor whose one-coordinate
matrix is `[[256,1],[1,256]]` is invertible over the integers, so some truth
table detects that trade.  We again take the numerically first witness.
-/

/-- Enumerate a truth table by the numerical codes of its `q`-bit inputs and
transport Boolean outputs to `Fin 2`. -/
def blockParityTableVector
    {q : Nat} (table : BitVec q -> Bool) :
    Fin (blockParityPrefixCount q) -> Fin 2 :=
  fun coordinate =>
    finTwoEquiv.symm (table (binaryAssignment q coordinate.val))

/-- Decode a binary vector indexed by input codes back to a truth table. -/
def blockParityVectorTable
    {q : Nat} (vector : Fin (blockParityPrefixCount q) -> Fin 2) :
    BitVec q -> Bool :=
  fun label => finTwoEquiv
    (vector ⟨binaryAssignmentValue label, by
      simpa [blockParityPrefixCount] using
        binaryAssignmentValue_lt_two_pow label⟩)

@[simp]
theorem blockParityVectorTable_tableVector
    {q : Nat} (table : BitVec q -> Bool) :
    blockParityVectorTable (blockParityTableVector table) = table := by
  funext label
  simp [blockParityVectorTable, blockParityTableVector,
    binaryAssignment_binaryAssignmentValue]

@[simp]
theorem blockParityTableVector_vectorTable
    {q : Nat} (vector : Fin (blockParityPrefixCount q) -> Fin 2) :
    blockParityTableVector (blockParityVectorTable vector) = vector := by
  funext coordinate
  simp [blockParityTableVector, blockParityVectorTable,
    binaryAssignmentValue_binaryAssignment_of_lt coordinate.isLt]

/-- Truth tables and binary vectors indexed by their input codes are
computably equivalent. -/
def blockParityTableVectorEquiv (q : Nat) :
    (BitVec q -> Bool) ≃ (Fin (blockParityPrefixCount q) -> Fin 2) where
  toFun := blockParityTableVector
  invFun := blockParityVectorTable
  left_inv := blockParityVectorTable_tableVector
  right_inv := blockParityTableVector_vectorTable

/-- Numerical candidate codes are equivalently binary vectors of width
`N = 2^q`. -/
def blockParityCandidateVectorEquiv (q : Nat) :
    BlockParityCandidateCode q ≃
      (Fin (blockParityPrefixCount q) -> Fin 2) :=
  (blockParityCandidateEquiv q).trans (blockParityTableVectorEquiv q)

theorem blockParityCandidateVectorEquiv_apply
    (q : Nat) (candidate : BlockParityCandidateCode q) :
    blockParityCandidateVectorEquiv q candidate =
      blockParityTableVector (blockParityTruthTable candidate) :=
  rfl

/-- The ordinary Hamming distance between two truth tables, computed through
the canonical enumeration of their `2^q` inputs. -/
def blockParityHammingDistance
    {q : Nat} (left right : BitVec q -> Bool) : Nat :=
  ((Finset.univ : Finset (Fin (blockParityPrefixCount q))).filter
    fun coordinate =>
      blockParityTableVector left coordinate ≠
        blockParityTableVector right coordinate).card

theorem binaryAgreementCount_tableVector_eq
    {q : Nat} (left right : BitVec q -> Bool) :
    binaryAgreementCount
        (blockParityTableVector left) (blockParityTableVector right) =
      blockParityPrefixCount q - blockParityHammingDistance left right := by
  classical
  have hPartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (blockParityPrefixCount q))))
    (p := fun coordinate =>
      blockParityTableVector left coordinate =
        blockParityTableVector right coordinate)
  have hPartition' :
      binaryAgreementCount
          (blockParityTableVector left) (blockParityTableVector right) +
        blockParityHammingDistance left right =
          blockParityPrefixCount q := by
    simpa only [binaryAgreementCount, blockParityHammingDistance,
      Finset.card_univ, Fintype.card_fin] using hPartition
  omega

theorem blockParityHammingDistance_comm
    {q : Nat} (left right : BitVec q -> Bool) :
    blockParityHammingDistance left right =
      blockParityHammingDistance right left := by
  unfold blockParityHammingDistance
  congr 1
  ext coordinate
  simp [eq_comm]

theorem binaryAgreementKernel_tableVector_eq
    {q : Nat} (left right : BitVec q -> Bool) :
    binaryAgreementKernel 256
        (blockParityTableVector left) (blockParityTableVector right) =
      256 ^ (blockParityPrefixCount q -
        blockParityHammingDistance left right) := by
  rw [binaryAgreementKernel_eq_pow_agreementCount,
    binaryAgreementCount_tableVector_eq]

/-- Conjugate the 256-agreement tensor into the numerical candidate-code
basis. -/
def blockParityAgreementTransformCode
    (q : Nat) (coefficient : BlockParityCandidateCode q -> ℤ)
    (test : BlockParityCandidateCode q) : ℤ :=
  ∑ candidate : BlockParityCandidateCode q,
    binaryAgreementKernel 256
      (blockParityCandidateVectorEquiv q test)
      (blockParityCandidateVectorEquiv q candidate) *
        coefficient candidate

theorem blockParityAgreementTransformCode_eq
    (q : Nat) (coefficient : BlockParityCandidateCode q -> ℤ)
    (test : BlockParityCandidateCode q) :
    blockParityAgreementTransformCode q coefficient test =
      binaryAgreementTransform 256
        (fun vector => coefficient
          ((blockParityCandidateVectorEquiv q).symm vector))
        (blockParityCandidateVectorEquiv q test) := by
  unfold blockParityAgreementTransformCode binaryAgreementTransform
  simpa using (blockParityCandidateVectorEquiv q).sum_comp
    (fun vector =>
      binaryAgreementKernel 256
        (blockParityCandidateVectorEquiv q test) vector *
      coefficient ((blockParityCandidateVectorEquiv q).symm vector))

theorem blockParityAgreementTransformCode_injective (q : Nat) :
    Function.Injective (blockParityAgreementTransformCode q) := by
  intro left right hTransforms
  let equivalence := blockParityCandidateVectorEquiv q
  have hConjugated :
      binaryAgreementTransform 256
          (fun vector => left (equivalence.symm vector)) =
        binaryAgreementTransform 256
          (fun vector => right (equivalence.symm vector)) := by
    funext testVector
    let testCode := equivalence.symm testVector
    have hAt := congrFun hTransforms testCode
    rw [blockParityAgreementTransformCode_eq,
      blockParityAgreementTransformCode_eq] at hAt
    simpa [equivalence, testCode] using hAt
  have hCoefficients := binaryAgreementTransform_256_injective hConjugated
  funext candidate
  have hAt := congrFun hCoefficients (equivalence candidate)
  simpa [equivalence] using hAt

theorem exists_blockParityAgreementDetectingCode
    (q : Nat) (hq : 64 ≤ q) :
    ∃ test : BlockParityCandidateCode q,
      blockParityAgreementTransformCode q
        (blockParityTradeCoefficientCode q hq) test ≠ 0 := by
  by_contra hNone
  push_neg at hNone
  have hZero :
      blockParityAgreementTransformCode q
          (blockParityTradeCoefficientCode q hq) = 0 := by
    funext test
    exact hNone test
  apply blockParityTradeCoefficient_ne_zero q hq
  funext table
  unfold blockParityTradeCoefficient
  have hCodeZero : blockParityTradeCoefficientCode q hq = 0 := by
    apply blockParityAgreementTransformCode_injective q
    funext test
    rw [congrFun hZero test]
    simp [blockParityAgreementTransformCode]
  exact congrFun hCodeZero (blockParityTruthTableCode table)

def blockParityDetectingCodes
    (q : Nat) (hq : 64 ≤ q) : Finset (BlockParityCandidateCode q) :=
  Finset.univ.filter fun test =>
    blockParityAgreementTransformCode q
      (blockParityTradeCoefficientCode q hq) test ≠ 0

theorem blockParityDetectingCodes_nonempty
    (q : Nat) (hq : 64 ≤ q) :
    (blockParityDetectingCodes q hq).Nonempty := by
  rcases exists_blockParityAgreementDetectingCode q hq with ⟨test, hTest⟩
  exact ⟨test, by simp [blockParityDetectingCodes, hTest]⟩

/-- The numerically first truth table which detects the canonical trade. -/
def blockParityCanonicalTestCode
    (q : Nat) (hq : 64 ≤ q) : BlockParityCandidateCode q :=
  (blockParityDetectingCodes q hq).min'
    (blockParityDetectingCodes_nonempty q hq)

/-- The requested canonical detecting truth table `t_q`. -/
def blockParityCanonicalTest
    (q : Nat) (hq : 64 ≤ q) : BitVec q -> Bool :=
  blockParityTruthTable (blockParityCanonicalTestCode q hq)

theorem blockParityCanonicalTestCode_detects
    (q : Nat) (hq : 64 ≤ q) :
    blockParityAgreementTransformCode q
        (blockParityTradeCoefficientCode q hq)
        (blockParityCanonicalTestCode q hq) ≠ 0 := by
  have hMem : blockParityCanonicalTestCode q hq ∈
      blockParityDetectingCodes q hq := Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hMem).2

/-- The exact truth-table-indexed sum appearing in the lower-bound target. -/
def blockParityAgreementObjective
    (q : Nat) (hq : 64 ≤ q) (test : BitVec q -> Bool) : ℤ :=
  ∑ table : BitVec q -> Bool,
    blockParityTradeCoefficient q hq table *
      256 ^ (blockParityPrefixCount q -
        blockParityHammingDistance table test)

theorem blockParityAgreementObjective_eq_transformCode
    (q : Nat) (hq : 64 ≤ q) (test : BitVec q -> Bool) :
    blockParityAgreementObjective q hq test =
      blockParityAgreementTransformCode q
        (blockParityTradeCoefficientCode q hq)
        (blockParityTruthTableCode test) := by
  unfold blockParityAgreementObjective blockParityAgreementTransformCode
  rw [← (blockParityCandidateEquiv q).sum_comp]
  apply Finset.sum_congr rfl
  intro candidate _
  rw [blockParityCandidateVectorEquiv_apply,
    blockParityCandidateVectorEquiv_apply,
    binaryAgreementKernel_tableVector_eq]
  simp [blockParityCandidateEquiv, blockParityTradeCoefficient,
    blockParityHammingDistance_comm, mul_comm]

/-- The canonical test detects the canonical kernel vector by the
`256^(N-d_H)` functional. -/
theorem blockParityAgreementObjective_canonical_ne_zero
    (q : Nat) (hq : 64 ≤ q) :
    blockParityAgreementObjective q hq
      (blockParityCanonicalTest q hq) ≠ 0 := by
  rw [blockParityAgreementObjective_eq_transformCode]
  simpa [blockParityCanonicalTest] using
    blockParityCanonicalTestCode_detects q hq

/-- The exact canonical witness promised by the block-parity construction:
`b_q` is nonzero, every row of `M_(q,q^2)` annihilates it, and `t_q` detects
it through the `256^(2^q-d_H)` functional. -/
theorem blockParityCanonicalTradeWitness
    (q : Nat) (hq : 64 ≤ q) :
    blockParityTradeCoefficient q hq ≠ 0 ∧
      (∀ profile : BlockParityNatProfile q (blockParityHiddenBudget q),
        blockParityMatrixAction q (blockParityHiddenBudget q)
          (fun candidate => blockParityTradeCoefficient q hq
            (blockParityTruthTable candidate)) profile = 0) ∧
      blockParityAgreementObjective q hq
        (blockParityCanonicalTest q hq) ≠ 0 := by
  exact ⟨blockParityTradeCoefficient_ne_zero q hq,
    blockParityMatrixAction_truthTableTrade_eq_zero q hq,
    blockParityAgreementObjective_canonical_ne_zero q hq⟩

end KLocality
