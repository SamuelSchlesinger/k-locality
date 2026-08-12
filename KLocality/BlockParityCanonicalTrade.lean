import KLocality.BlockParityCounting

namespace KLocality

open scoped BigOperators

/-!
# A canonical block-parity marginal trade

The counting argument only asserts that two subset histograms collide.  This
file turns that assertion into data: among all ordered colliding pairs, take
the lexicographically least one.  Its signed indicator is a nonzero integer
vector in the kernel of the complete cubic profile matrix.
-/

abbrev BlockParitySubsetCode (q : Nat) :=
  Fin (2 ^ blockParityCandidateCount q)

abbrev BlockParityCollisionPairCode (q : Nat) :=
  Fin ((2 ^ blockParityCandidateCount q) *
    (2 ^ blockParityCandidateCount q))

def blockParityCollisionPairEquiv (q : Nat) :
    BlockParitySubsetCode q × BlockParitySubsetCode q ≃
      BlockParityCollisionPairCode q :=
  finProdFinEquiv

def blockParityDecodeCollisionPair
    (q : Nat) (code : BlockParityCollisionPairCode q) :
    BlockParitySubsetCode q × BlockParitySubsetCode q :=
  (blockParityCollisionPairEquiv q).symm code

@[simp]
theorem blockParityDecodeCollisionPair_encode
    (q : Nat) (pair : BlockParitySubsetCode q × BlockParitySubsetCode q) :
    blockParityDecodeCollisionPair q (blockParityCollisionPairEquiv q pair) = pair :=
  (blockParityCollisionPairEquiv q).symm_apply_apply pair

/-- Decidable collision predicate used by the exhaustive finite search. -/
def blockParityIsCollision
    (q : Nat) (code : BlockParityCollisionPairCode q) : Bool :=
  let pair := blockParityDecodeCollisionPair q code
  decide (pair.1 ≠ pair.2) &&
    decide (blockParitySubsetHistogram q (blockParityHiddenBudget q) pair.1 =
      blockParitySubsetHistogram q (blockParityHiddenBudget q) pair.2)

/-- The finite search space of ordered, distinct histogram collisions. -/
def blockParityCollisionPairs (q : Nat) :
    Finset (BlockParityCollisionPairCode q) :=
  Finset.univ.filter fun code => blockParityIsCollision q code = true

theorem blockParityCollisionPairs_nonempty
    {q : Nat} (hq : 64 ≤ q) :
    (blockParityCollisionPairs q).Nonempty := by
  rcases exists_blockParitySubsetHistogram_collision hq with
    ⟨left, right, hNe, hHistogram⟩
  refine ⟨blockParityCollisionPairEquiv q (left, right), ?_⟩
  simp [blockParityCollisionPairs, blockParityIsCollision, hNe, hHistogram]

/-- The lexicographically first ordered collision.  This is a finite
exhaustive-search definition, with `hq` supplying only its nonemptiness. -/
def blockParityCanonicalCollision
    (q : Nat) (hq : 64 ≤ q) :
    BlockParitySubsetCode q × BlockParitySubsetCode q :=
  blockParityDecodeCollisionPair q
    ((blockParityCollisionPairs q).min'
      (blockParityCollisionPairs_nonempty hq))

theorem blockParityCanonicalCollisionCode_mem
    (q : Nat) (hq : 64 ≤ q) :
    (blockParityCollisionPairs q).min'
        (blockParityCollisionPairs_nonempty hq) ∈
      blockParityCollisionPairs q := by
  exact Finset.min'_mem _ _

theorem blockParityCanonicalCollision_isCollision
    (q : Nat) (hq : 64 ≤ q) :
    blockParityIsCollision q
        ((blockParityCollisionPairs q).min'
          (blockParityCollisionPairs_nonempty hq)) = true := by
  exact (Finset.mem_filter.mp
    (blockParityCanonicalCollisionCode_mem q hq)).2

theorem blockParityCanonicalCollision_ne
    (q : Nat) (hq : 64 ≤ q) :
    (blockParityCanonicalCollision q hq).1 ≠
      (blockParityCanonicalCollision q hq).2 := by
  have hCollision := blockParityCanonicalCollision_isCollision q hq
  simp only [blockParityIsCollision,
    Bool.and_eq_true, decide_eq_true_eq] at hCollision
  exact hCollision.1

theorem blockParityCanonicalCollision_histogram_eq
    (q : Nat) (hq : 64 ≤ q) :
    blockParitySubsetHistogram q (blockParityHiddenBudget q)
        (blockParityCanonicalCollision q hq).1 =
      blockParitySubsetHistogram q (blockParityHiddenBudget q)
        (blockParityCanonicalCollision q hq).2 := by
  have hCollision := blockParityCanonicalCollision_isCollision q hq
  simp only [blockParityIsCollision,
    Bool.and_eq_true, decide_eq_true_eq] at hCollision
  exact hCollision.2

/-- Signed incidence vector of the canonical collision, indexed numerically
by truth tables.  Every coefficient lies in `{-1,0,1}`. -/
def blockParityTradeCoefficientCode
    (q : Nat) (hq : 64 ≤ q) (candidate : BlockParityCandidateCode q) : ℤ :=
  (if blockParitySubsetContains
      (blockParityCanonicalCollision q hq).1 candidate then 1 else 0) -
    (if blockParitySubsetContains
      (blockParityCanonicalCollision q hq).2 candidate then 1 else 0)

/-- The same signed trade in the truth-table indexing requested by the
asymptotic statement. -/
def blockParityTradeCoefficient
    (q : Nat) (hq : 64 ≤ q) (table : BitVec q -> Bool) : ℤ :=
  blockParityTradeCoefficientCode q hq (blockParityTruthTableCode table)

theorem blockParitySubsetContains_injective (q : Nat) :
    Function.Injective
      (fun subset : BlockParitySubsetCode q =>
        fun candidate : BlockParityCandidateCode q =>
          blockParitySubsetContains subset candidate) := by
  intro left right hMembership
  apply Fin.ext
  have hValue := congrArg binaryAssignmentValue hMembership
  unfold blockParitySubsetContains at hValue
  rw [binaryAssignmentValue_binaryAssignment_of_lt left.isLt,
    binaryAssignmentValue_binaryAssignment_of_lt right.isLt] at hValue
  exact hValue

theorem exists_blockParityTradeCoefficientCode_ne_zero
    (q : Nat) (hq : 64 ≤ q) :
    ∃ candidate : BlockParityCandidateCode q,
      blockParityTradeCoefficientCode q hq candidate ≠ 0 := by
  have hSubsets := blockParityCanonicalCollision_ne q hq
  have hMembership :
      (fun candidate : BlockParityCandidateCode q =>
          blockParitySubsetContains
            (blockParityCanonicalCollision q hq).1 candidate) ≠
        (fun candidate : BlockParityCandidateCode q =>
          blockParitySubsetContains
            (blockParityCanonicalCollision q hq).2 candidate) := by
    intro hEqual
    exact hSubsets (blockParitySubsetContains_injective q hEqual)
  have hCoordinate :
      ∃ candidate : BlockParityCandidateCode q,
        blockParitySubsetContains
            (blockParityCanonicalCollision q hq).1 candidate ≠
          blockParitySubsetContains
            (blockParityCanonicalCollision q hq).2 candidate := by
    by_contra hNone
    push_neg at hNone
    exact hMembership (funext hNone)
  rcases hCoordinate with ⟨candidate, hCandidate⟩
  refine ⟨candidate, ?_⟩
  unfold blockParityTradeCoefficientCode
  cases hLeft : blockParitySubsetContains
      (blockParityCanonicalCollision q hq).1 candidate <;>
    cases hRight : blockParitySubsetContains
      (blockParityCanonicalCollision q hq).2 candidate <;>
    simp_all

theorem blockParityTradeCoefficient_ne_zero
    (q : Nat) (hq : 64 ≤ q) :
    blockParityTradeCoefficient q hq ≠ 0 := by
  rcases exists_blockParityTradeCoefficientCode_ne_zero q hq with
    ⟨candidate, hCandidate⟩
  intro hZero
  have hAt := congrFun hZero (blockParityTruthTable candidate)
  simp only [blockParityTradeCoefficient,
    blockParityTruthTableCode_truthTable] at hAt
  exact hCandidate hAt

/-- The integer action of the complete cubic-profile matrix on a coefficient
vector. -/
def blockParityMatrixAction
    (q latentBits : Nat)
    (coefficient : BlockParityCandidateCode q -> ℤ)
    (profile : BlockParityNatProfile q latentBits) : ℤ :=
  ∑ candidate : BlockParityCandidateCode q,
    ((blockParityColumn q latentBits candidate).count profile : ℤ) *
      coefficient candidate

private theorem selectedColumnSum_eq_subsetProfileCount
    (q latentBits : Nat) (subset : BlockParitySubsetCode q)
    (profile : BlockParityNatProfile q latentBits) :
    (∑ candidate : BlockParityCandidateCode q,
        ((blockParityColumn q latentBits candidate).count profile : ℤ) *
          (if blockParitySubsetContains subset candidate then 1 else 0)) =
      (blockParitySubsetProfileCount q latentBits subset profile : ℤ) := by
  unfold blockParitySubsetProfileCount
  push_cast
  apply Finset.sum_congr rfl
  intro candidate _
  cases hSelected : blockParitySubsetContains subset candidate <;>
    simp

/-- The canonical signed incidence vector is annihilated by every row of
the full matrix `M_(q,q^2)`. -/
theorem blockParityMatrixAction_trade_eq_zero
    (q : Nat) (hq : 64 ≤ q)
    (profile : BlockParityNatProfile q (blockParityHiddenBudget q)) :
    blockParityMatrixAction q (blockParityHiddenBudget q)
        (blockParityTradeCoefficientCode q hq) profile = 0 := by
  have hHistogram := congrFun
    (blockParityCanonicalCollision_histogram_eq q hq) profile
  have hCount :
      blockParitySubsetProfileCount q (blockParityHiddenBudget q)
          (blockParityCanonicalCollision q hq).1 profile =
        blockParitySubsetProfileCount q (blockParityHiddenBudget q)
          (blockParityCanonicalCollision q hq).2 profile := by
    exact Fin.ext_iff.mp hHistogram
  unfold blockParityMatrixAction blockParityTradeCoefficientCode
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,
    selectedColumnSum_eq_subsetProfileCount,
    selectedColumnSum_eq_subsetProfileCount]
  exact sub_eq_zero.mpr (congrArg Int.ofNat hCount)

/-- Truth-table-indexed form of the preceding kernel identity. -/
theorem blockParityMatrixAction_truthTableTrade_eq_zero
    (q : Nat) (hq : 64 ≤ q)
    (profile : BlockParityNatProfile q (blockParityHiddenBudget q)) :
    blockParityMatrixAction q (blockParityHiddenBudget q)
        (fun candidate => blockParityTradeCoefficient q hq
          (blockParityTruthTable candidate)) profile = 0 := by
  simpa [blockParityTradeCoefficient] using
    blockParityMatrixAction_trade_eq_zero q hq profile

end KLocality
