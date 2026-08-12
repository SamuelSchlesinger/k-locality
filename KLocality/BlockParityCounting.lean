import KLocality.BlockParityMatrix
import KLocality.UniformExplicitCubicLowerBound

namespace KLocality

open scoped BigOperators

set_option maxHeartbeats 1000000

/-!
# Counting collisions at a quadratic hidden budget

For `q` prefix bits we take the hidden-bit budget `L(q)=q^2`.  The number of
candidate columns is `2^(2^q)`, while the complete expanded cubic-profile
space is small enough that subsets of columns must collide once `q >= 64`.
-/

def blockParityHiddenBudget (q : Nat) : Nat := q ^ 2

theorem blockParityHiddenBudget_superlinear :
    ∀ constant : Nat, ∃ threshold : Nat, ∀ q,
      threshold ≤ q ->
        constant * (q + 5) < blockParityHiddenBudget q := by
  intro constant
  refine ⟨2 * constant + 6, ?_⟩
  intro q hq
  unfold blockParityHiddenBudget
  nlinarith [Nat.zero_le constant]

theorem blockParityDegree_eq_two_pow (q : Nat) :
    blockParityDegree q = 2 ^ (q + 3) := by
  unfold blockParityDegree blockParityPrefixCount
  rw [pow_add]
  norm_num

theorem blockParityDegree_add_one_le_two_pow (q : Nat) :
    blockParityDegree q + 1 ≤ 2 ^ (q + 4) := by
  rw [blockParityDegree_eq_two_pow]
  exact Nat.succ_le_iff.mpr
    (Nat.pow_lt_pow_right (by omega) (by omega))

theorem blockParityJointScope_card_le (q latentBits : Nat) :
    Fintype.card (BlockParityJointScope q latentBits) ≤
      (q + latentBits + 6) ^ 3 := by
  have hBound := cubicFeatureScope_card_le
    (Sum (BlockParityVar q) (Fin latentBits))
  simpa [BlockParityJointScope, BlockParityVar, Fintype.card_sum,
    Fintype.card_fin, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBound

theorem blockParityNatProfile_card (q latentBits : Nat) :
    Fintype.card (BlockParityNatProfile q latentBits) =
      (blockParityDegree q + 1) ^
        Fintype.card (BlockParityJointScope q latentBits) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_fun,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem blockParityNatProfile_card_le_two_pow (q latentBits : Nat) :
    Fintype.card (BlockParityNatProfile q latentBits) ≤
      2 ^ ((q + 4) * (q + latentBits + 6) ^ 3) := by
  rw [blockParityNatProfile_card]
  calc
    (blockParityDegree q + 1) ^
        Fintype.card (BlockParityJointScope q latentBits) ≤
        (2 ^ (q + 4)) ^
          Fintype.card (BlockParityJointScope q latentBits) :=
      Nat.pow_le_pow_left (blockParityDegree_add_one_le_two_pow q) _
    _ ≤ (2 ^ (q + 4)) ^ ((q + latentBits + 6) ^ 3) :=
      Nat.pow_le_pow_right (by positivity)
        (blockParityJointScope_card_le q latentBits)
    _ = 2 ^ ((q + 4) * (q + latentBits + 6) ^ 3) := by
      exact (pow_mul 2 (q + 4) ((q + latentBits + 6) ^ 3)).symm

def blockParityCoordinateLog (q latentBits : Nat) : Nat :=
  blockParityPrefixCount q + latentBits * blockParityDegree q + 1

theorem blockParityHistogramCoordinateBound_le_two_pow
    (q latentBits : Nat) :
    blockParityHistogramCoordinateBound q latentBits ≤
      2 ^ blockParityCoordinateLog q latentBits := by
  unfold blockParityHistogramCoordinateBound blockParityCandidateCount
  unfold blockParityCoordinateLog
  rw [← pow_add]
  rw [show blockParityPrefixCount q +
      latentBits * blockParityDegree q + 1 =
        (blockParityPrefixCount q +
          latentBits * blockParityDegree q) + 1 by omega]
  rw [pow_succ]
  have hPositive :
      0 < 2 ^ (blockParityPrefixCount q +
        latentBits * blockParityDegree q) := by positivity
  omega

theorem blockParityCoordinateLog_quadratic_le (q : Nat) :
    blockParityCoordinateLog q (blockParityHiddenBudget q) ≤
      2 ^ (3 * q + 5) := by
  have hQ : q ≤ 2 ^ q := Nat.lt_two_pow_self.le
  have hQSq : q ^ 2 ≤ 2 ^ (2 * q) := by
    calc
      q ^ 2 = q * q := by ring
      _ ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul hQ hQ
      _ = 2 ^ (2 * q) := by
        rw [← pow_add]
        congr 1
        omega
  have hPrefix : blockParityPrefixCount q ≤ 2 ^ (3 * q + 3) := by
    unfold blockParityPrefixCount
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hLatent :
      blockParityHiddenBudget q * blockParityDegree q ≤
        2 ^ (3 * q + 3) := by
    unfold blockParityHiddenBudget
    rw [blockParityDegree_eq_two_pow]
    calc
      q ^ 2 * 2 ^ (q + 3) ≤ 2 ^ (2 * q) * 2 ^ (q + 3) :=
        Nat.mul_le_mul_right _ hQSq
      _ = 2 ^ (3 * q + 3) := by
        rw [← pow_add]
        congr 1
        omega
  have hPowerPositive : 0 < 2 ^ (3 * q + 3) := by positivity
  calc
    blockParityCoordinateLog q (blockParityHiddenBudget q) ≤
        2 ^ (3 * q + 3) + 2 ^ (3 * q + 3) + 1 := by
      unfold blockParityCoordinateLog
      omega
    _ ≤ 4 * 2 ^ (3 * q + 3) := by omega
    _ = 2 ^ (3 * q + 5) := by
      calc
        4 * 2 ^ (3 * q + 3) = 2 ^ 2 * 2 ^ (3 * q + 3) := by rfl
        _ = 2 ^ (2 + (3 * q + 3)) :=
          (pow_add 2 2 (3 * q + 3)).symm
        _ = 2 ^ (3 * q + 5) := by
          congr 1
          omega

/-- Exponent which dominates the complete histogram count. -/
def blockParityDominationPolynomial (q : Nat) : Nat :=
  (q + 4) * (q ^ 2 + q + 6) ^ 3 + (3 * q + 5)

theorem blockParityDominationPolynomial_succ_le_double
    {q : Nat} (hq : 9 ≤ q) :
    blockParityDominationPolynomial (q + 1) ≤
      2 * blockParityDominationPolynomial q := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hq
  have hIdentity :
      2 * blockParityDominationPolynomial (9 + offset) =
        blockParityDominationPolynomial ((9 + offset) + 1) +
          (offset ^ 7 + 63 * offset ^ 6 + 1671 * offset ^ 5 +
            23981 * offset ^ 4 + 197996 * offset ^ 3 +
            911208 * offset ^ 2 + 1998499 * offset + 1150621) := by
    unfold blockParityDominationPolynomial
    ring
  omega

theorem blockParityDominationPolynomial_64_lt :
    blockParityDominationPolynomial 64 < 2 ^ 64 := by
  norm_num [blockParityDominationPolynomial]

theorem blockParityDominationPolynomial_add_64_lt_two_pow
    (offset : Nat) :
    blockParityDominationPolynomial (64 + offset) < 2 ^ (64 + offset) := by
  induction offset with
  | zero => simpa using blockParityDominationPolynomial_64_lt
  | succ offset ih =>
      calc
        blockParityDominationPolynomial (64 + (offset + 1)) =
            blockParityDominationPolynomial ((64 + offset) + 1) := by
          congr 1
        _ ≤ 2 * blockParityDominationPolynomial (64 + offset) :=
          blockParityDominationPolynomial_succ_le_double (by omega)
        _ < 2 * 2 ^ (64 + offset) :=
          Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 2 ^ (64 + offset) * 2 :=
          Nat.mul_comm _ _
        _ = 2 ^ ((64 + offset) + 1) := (pow_succ 2 _).symm
        _ = 2 ^ (64 + (offset + 1)) := by
          exact congrArg (fun exponent : Nat => 2 ^ exponent) (by omega)

theorem blockParityDominationPolynomial_lt_two_pow
    {q : Nat} (hq : 64 ≤ q) :
    blockParityDominationPolynomial q < 2 ^ q := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hq
  exact blockParityDominationPolynomial_add_64_lt_two_pow offset

theorem blockParityHistogramExponent_lt_candidateCount
    {q : Nat} (hq : 64 ≤ q) :
    blockParityCoordinateLog q (blockParityHiddenBudget q) *
        Fintype.card
          (BlockParityNatProfile q (blockParityHiddenBudget q)) <
      blockParityCandidateCount q := by
  have hProfile := blockParityNatProfile_card_le_two_pow
    q (blockParityHiddenBudget q)
  have hCoordinate := blockParityCoordinateLog_quadratic_le q
  calc
    blockParityCoordinateLog q (blockParityHiddenBudget q) *
        Fintype.card
          (BlockParityNatProfile q (blockParityHiddenBudget q)) ≤
        2 ^ (3 * q + 5) *
          2 ^ ((q + 4) *
            (q + blockParityHiddenBudget q + 6) ^ 3) :=
      Nat.mul_le_mul hCoordinate hProfile
    _ = 2 ^ blockParityDominationPolynomial q := by
      rw [← pow_add]
      unfold blockParityDominationPolynomial blockParityHiddenBudget
      congr 1
      ring
    _ < 2 ^ (2 ^ q) :=
      Nat.pow_lt_pow_right (by omega)
        (blockParityDominationPolynomial_lt_two_pow hq)
    _ = blockParityCandidateCount q := by
      rfl

theorem blockParityHistogram_card (q latentBits : Nat) :
    Fintype.card (BlockParityHistogram q latentBits) =
      blockParityHistogramCoordinateBound q latentBits ^
        Fintype.card (BlockParityNatProfile q latentBits) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_fun,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- At hidden budget `q^2`, the complete histogram space is smaller than the
powerset of block-parity columns. -/
theorem blockParity_histogram_cardinality_bound
    {q : Nat} (hq : 64 ≤ q) :
    Fintype.card (BlockParityHistogram q (blockParityHiddenBudget q)) <
      2 ^ blockParityCandidateCount q := by
  rw [blockParityHistogram_card]
  calc
    blockParityHistogramCoordinateBound q (blockParityHiddenBudget q) ^
        Fintype.card
          (BlockParityNatProfile q (blockParityHiddenBudget q)) ≤
        (2 ^ blockParityCoordinateLog q (blockParityHiddenBudget q)) ^
          Fintype.card
            (BlockParityNatProfile q (blockParityHiddenBudget q)) :=
      Nat.pow_le_pow_left
        (blockParityHistogramCoordinateBound_le_two_pow
          q (blockParityHiddenBudget q)) _
    _ = 2 ^ (blockParityCoordinateLog q (blockParityHiddenBudget q) *
        Fintype.card
          (BlockParityNatProfile q (blockParityHiddenBudget q))) := by
      exact (pow_mul 2 _ _).symm
    _ < 2 ^ blockParityCandidateCount q :=
      Nat.pow_lt_pow_right (by omega)
        (blockParityHistogramExponent_lt_candidateCount hq)

/-- Two distinct encoded subsets have exactly the same sum of columns of
`M_(q,q^2)`. -/
theorem exists_blockParitySubsetHistogram_collision
    {q : Nat} (hq : 64 ≤ q) :
    ∃ left right : Fin (2 ^ blockParityCandidateCount q),
      left ≠ right ∧
        blockParitySubsetHistogram q (blockParityHiddenBudget q) left =
          blockParitySubsetHistogram q (blockParityHiddenBudget q) right := by
  have hCard :
      Fintype.card
          (BlockParityHistogram q (blockParityHiddenBudget q)) <
        Fintype.card (Fin (2 ^ blockParityCandidateCount q)) := by
    simpa using blockParity_histogram_cardinality_bound hq
  have hNotInjective :
      ¬Function.Injective
        (blockParitySubsetHistogram q (blockParityHiddenBudget q)) :=
    Fintype.not_injective_of_card_lt _ hCard
  simp only [Function.Injective] at hNotInjective
  push_neg at hNotInjective
  rcases hNotInjective with ⟨left, right, hEqual, hNe⟩
  exact ⟨left, right, hNe, hEqual⟩

end KLocality
