import KLocality.ExplicitCubicLowerBound
import Mathlib.Data.Fintype.Powerset

namespace KLocality

open scoped BigOperators

set_option maxRecDepth 30000

/-!
# Superlinear explicit full-support cubic lower-bound families

This file parameterizes the finite-profile pigeonhole mechanism from
`ExplicitCubicLowerBound`.  For every hidden-bit budget `budget`, it constructs
an explicit full-support rational distribution on `budget + 64` visible bits
and proves that every cubic localization uses more than `budget` hidden bits.
The same generic inequality is then specialized more aggressively: on
`4 * scale + 24` visible bits, the very same closed-form table requires more
than `2 ^ scale` hidden bits.  Thus the checked lower bound is exponential in
the visible dimension (with exponent `1/4`), and in particular eventually
larger than its square.

The constants are deliberately loose.  The counting mechanism itself points
toward exponent `1/3`; this file chooses `1/4` to keep the uniform natural-
number inequalities short and robust.  Certificate degree and extraction are
also not optimized.
-/

/-! ## Cubic feature-scope counting -/

/-- Encode a scope of cardinality at most three by an arbitrarily enumerated,
`Option`-padded triple.  Equality of encodings recovers membership and hence
the original finset. -/
noncomputable def cubicScopeCode
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (scope : FeatureScope Var 3) : Fin 3 → Option Var :=
  fun index =>
    if hIndex : index.val < scope.1.card then
      some (scope.1.equivFin.symm ⟨index.val, hIndex⟩).1
    else none

theorem cubicScopeCode_injective
    {Var : Type*} [Fintype Var] [DecidableEq Var] :
    Function.Injective (cubicScopeCode (Var := Var)) := by
  classical
  intro left right hCode
  apply Subtype.ext
  ext value
  constructor
  · intro hLeft
    let source : left.1 := ⟨value, hLeft⟩
    let sourceIndex : Fin left.1.card := left.1.equivFin source
    let index : Fin 3 :=
      ⟨sourceIndex.val, lt_of_lt_of_le sourceIndex.isLt left.2⟩
    have hLeftAt : cubicScopeCode left index = some value := by
      unfold cubicScopeCode
      rw [dif_pos sourceIndex.isLt]
      have hFin :
          (⟨index.val, sourceIndex.isLt⟩ : Fin left.1.card) =
            sourceIndex := Fin.ext rfl
      rw [hFin]
      exact congrArg (fun element : left.1 => some element.1)
        (left.1.equivFin.symm_apply_apply source)
    have hRightAt : cubicScopeCode right index = some value := by
      rw [← hCode]
      exact hLeftAt
    unfold cubicScopeCode at hRightAt
    split at hRightAt
    next hIndex =>
      have hValue :
          (right.1.equivFin.symm ⟨index.val, hIndex⟩).1 = value := by
        simpa using Option.some.inj hRightAt
      rw [← hValue]
      exact (right.1.equivFin.symm ⟨index.val, hIndex⟩).2
    next hIndex => simp at hRightAt
  · intro hRight
    have hReverse :
        cubicScopeCode right = cubicScopeCode left := hCode.symm
    exact (show right.1 ⊆ left.1 by
      intro candidate hCandidate
      let source : right.1 := ⟨candidate, hCandidate⟩
      let sourceIndex : Fin right.1.card := right.1.equivFin source
      let index : Fin 3 :=
        ⟨sourceIndex.val, lt_of_lt_of_le sourceIndex.isLt right.2⟩
      have hRightAt : cubicScopeCode right index = some candidate := by
        unfold cubicScopeCode
        rw [dif_pos sourceIndex.isLt]
        have hFin :
            (⟨index.val, sourceIndex.isLt⟩ : Fin right.1.card) =
              sourceIndex := Fin.ext rfl
        rw [hFin]
        exact congrArg (fun element : right.1 => some element.1)
          (right.1.equivFin.symm_apply_apply source)
      have hLeftAt : cubicScopeCode left index = some candidate := by
        rw [← hReverse]
        exact hRightAt
      unfold cubicScopeCode at hLeftAt
      split at hLeftAt
      next hIndex =>
        have hValue :
            (left.1.equivFin.symm ⟨index.val, hIndex⟩).1 = candidate := by
          simpa using Option.some.inj hLeftAt
        rw [← hValue]
        exact (left.1.equivFin.symm ⟨index.val, hIndex⟩).2
      next hIndex => simp at hLeftAt) hRight

/-- There are at most `(q+1)^3` scopes of size at most three on a `q`-element
variable type. -/
theorem cubicFeatureScope_card_le
    (Var : Type*) [Fintype Var] [DecidableEq Var] :
    Fintype.card (FeatureScope Var 3) ≤
      (Fintype.card Var + 1) ^ 3 := by
  calc
    Fintype.card (FeatureScope Var 3) ≤
        Fintype.card (Fin 3 → Option Var) :=
      Fintype.card_le_of_injective (cubicScopeCode (Var := Var))
        cubicScopeCode_injective
    _ = (Fintype.card Var + 1) ^ 3 := by
      simp

/-! ## Uniform numerical parameters -/

/-- Visible dimension used for hidden-bit budget `budget`. -/
def uniformCubicVisibleBits (budget : Nat) : Nat := 64 + budget

/-- Number of non-filler visible cells. -/
def uniformCubicBlockCount (n : Nat) : Nat := 2 ^ n - 1

/-- Common degree of the binary-digit candidate monomials. -/
def uniformCubicDegree (n : Nat) : Nat := uniformCubicBlockCount n * 2

/-- Binary logarithm used to dominate one histogram coordinate. -/
def uniformCubicCoordinateLog (n latentBits : Nat) : Nat :=
  uniformCubicBlockCount n +
    latentBits * uniformCubicDegree n + 1

/-- A convenient power-of-two bound for the preceding logarithm. -/
def uniformCubicCoordinateLogLog (n latentBits : Nat) : Nat :=
  n + latentBits + 3

/-- Binary logarithm bounding the number of possible cubic profiles. -/
def uniformCubicProfileLog (n latentBits : Nat) : Nat :=
  (n + 1) * (n + latentBits + 1) ^ 3

/-- Polynomial appearing in the final exponential domination argument. -/
def uniformCubicDominationPolynomial (budget : Nat) : Nat :=
  (2 * budget + 67) + (budget + 65) * (2 * budget + 65) ^ 3 + 1

theorem uniformCubicDominationPolynomial_zero_lt_two_pow :
    uniformCubicDominationPolynomial 0 < 2 ^ 64 := by
  norm_num [uniformCubicDominationPolynomial]

theorem uniformCubicDominationPolynomial_succ_le_double (budget : Nat) :
    uniformCubicDominationPolynomial (budget + 1) ≤
      2 * uniformCubicDominationPolynomial budget := by
  unfold uniformCubicDominationPolynomial
  nlinarith [sq_nonneg budget, sq_nonneg (budget ^ 2)]

theorem uniformCubicDominationPolynomial_lt_two_pow (budget : Nat) :
    uniformCubicDominationPolynomial budget < 2 ^ (64 + budget) := by
  induction budget with
  | zero => exact uniformCubicDominationPolynomial_zero_lt_two_pow
  | succ budget ih =>
      calc
        uniformCubicDominationPolynomial (budget + 1) ≤
            uniformCubicDominationPolynomial budget +
              uniformCubicDominationPolynomial budget := by
          simpa [two_mul] using
          uniformCubicDominationPolynomial_succ_le_double budget
        _ < 2 ^ (64 + budget) + 2 ^ (64 + budget) :=
          Nat.add_lt_add ih ih
        _ = 2 ^ (64 + budget + 1) :=
          (Nat.two_pow_succ (64 + budget)).symm
        _ = 2 ^ (64 + (budget + 1)) := by
          congr 1

theorem uniformCubic_parameter_inequality
    {budget latentBits : Nat} (hLatent : latentBits ≤ budget) :
    uniformCubicCoordinateLogLog (uniformCubicVisibleBits budget) latentBits +
        uniformCubicProfileLog (uniformCubicVisibleBits budget) latentBits <
      uniformCubicBlockCount (uniformCubicVisibleBits budget) := by
  let n := uniformCubicVisibleBits budget
  have hPolynomial :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits + 1 ≤
        uniformCubicDominationPolynomial budget := by
    have hCoordinate :
        64 + budget + latentBits + 3 ≤ 2 * budget + 67 := by
      omega
    have hInside :
        64 + budget + latentBits + 1 ≤ 2 * budget + 65 := by
      omega
    have hProfile :
        (64 + budget + 1) * (64 + budget + latentBits + 1) ^ 3 ≤
          (budget + 65) * (2 * budget + 65) ^ 3 := by
      rw [show 64 + budget + 1 = budget + 65 by omega]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hInside 3)
    dsimp [n, uniformCubicVisibleBits, uniformCubicCoordinateLogLog,
      uniformCubicProfileLog, uniformCubicDominationPolynomial]
    exact Nat.add_le_add_right (Nat.add_le_add hCoordinate hProfile) 1
  have hPower := uniformCubicDominationPolynomial_lt_two_pow budget
  have hSucc :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits + 1 < 2 ^ n := by
    exact lt_of_le_of_lt hPolynomial (by simpa [n, uniformCubicVisibleBits] using hPower)
  have hPowPositive : 0 < 2 ^ n := by positivity
  unfold uniformCubicBlockCount
  change
    uniformCubicCoordinateLogLog n latentBits +
        uniformCubicProfileLog n latentBits < 2 ^ n - 1
  omega

/-! ## Bounds entering the histogram pigeonhole argument -/

theorem uniformCubicBlockCount_lt_two_pow (n : Nat) :
    uniformCubicBlockCount n < 2 ^ n := by
  unfold uniformCubicBlockCount
  have hPositive : 0 < 2 ^ n := by positivity
  omega

theorem uniformCubicDegree_lt_two_pow (n : Nat) :
    uniformCubicDegree n < 2 ^ (n + 1) := by
  unfold uniformCubicDegree
  calc
    uniformCubicBlockCount n * 2 < 2 ^ n * 2 :=
      (Nat.mul_lt_mul_right (by omega : 0 < 2)).2
        (uniformCubicBlockCount_lt_two_pow n)
    _ = 2 ^ (n + 1) := (pow_succ 2 n).symm

theorem uniformCubicDegree_add_one_le_two_pow (n : Nat) :
    uniformCubicDegree n + 1 ≤ 2 ^ (n + 1) :=
  Nat.succ_le_iff.mpr (uniformCubicDegree_lt_two_pow n)

theorem uniformCubicCoordinateLog_le_two_pow (n latentBits : Nat) :
    uniformCubicCoordinateLog n latentBits ≤
      2 ^ uniformCubicCoordinateLogLog n latentBits := by
  let power := 2 ^ (n + latentBits + 1)
  have hBlock : uniformCubicBlockCount n ≤ power := by
    calc
      uniformCubicBlockCount n ≤ 2 ^ n :=
        (uniformCubicBlockCount_lt_two_pow n).le
      _ ≤ 2 ^ (n + latentBits + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hLatent : latentBits ≤ 2 ^ latentBits :=
    latentBits.lt_two_pow_self.le
  have hDegree : uniformCubicDegree n ≤ 2 ^ (n + 1) :=
    (uniformCubicDegree_lt_two_pow n).le
  have hProduct :
      latentBits * uniformCubicDegree n ≤ power := by
    calc
      latentBits * uniformCubicDegree n ≤
          2 ^ latentBits * 2 ^ (n + 1) :=
        Nat.mul_le_mul hLatent hDegree
      _ = 2 ^ (n + latentBits + 1) := by
        rw [← pow_add]
        congr 1
        omega
  have hPowerPositive : 0 < power := by positivity
  calc
    uniformCubicCoordinateLog n latentBits ≤ power + power + 1 := by
      unfold uniformCubicCoordinateLog
      exact Nat.add_le_add_right (Nat.add_le_add hBlock hProduct) 1
    _ ≤ 4 * power := by omega
    _ = 2 ^ uniformCubicCoordinateLogLog n latentBits := by
      unfold uniformCubicCoordinateLogLog
      calc
        4 * power = 2 ^ 2 * 2 ^ (n + latentBits + 1) := by
          rfl
        _ = 2 ^ (2 + (n + latentBits + 1)) :=
          (pow_add 2 2 (n + latentBits + 1)).symm
        _ = 2 ^ (n + latentBits + 3) := by
          congr 1
          omega

abbrev UniformCubicJointScope (n latentBits : Nat) :=
  FeatureScope (Sum (Fin n) (Fin latentBits)) 3

theorem uniformCubicJointScope_card_le (n latentBits : Nat) :
    Fintype.card (UniformCubicJointScope n latentBits) ≤
      (n + latentBits + 1) ^ 3 := by
  simpa [UniformCubicJointScope] using
    cubicFeatureScope_card_le (Sum (Fin n) (Fin latentBits))

theorem uniformCubicProfileCount_le_two_pow (n latentBits : Nat) :
    (uniformCubicDegree n + 1) ^
        Fintype.card (UniformCubicJointScope n latentBits) ≤
      2 ^ uniformCubicProfileLog n latentBits := by
  let scopeBound := (n + latentBits + 1) ^ 3
  calc
    (uniformCubicDegree n + 1) ^
        Fintype.card (UniformCubicJointScope n latentBits) ≤
        (2 ^ (n + 1)) ^
          Fintype.card (UniformCubicJointScope n latentBits) :=
      Nat.pow_le_pow_left (uniformCubicDegree_add_one_le_two_pow n) _
    _ ≤ (2 ^ (n + 1)) ^ scopeBound :=
      Nat.pow_le_pow_right (by positivity)
        (uniformCubicJointScope_card_le n latentBits)
    _ = 2 ^ uniformCubicProfileLog n latentBits := by
      unfold scopeBound uniformCubicProfileLog
      exact (pow_mul 2 (n + 1) ((n + latentBits + 1) ^ 3)).symm

/-- The powerset of binary-digit candidates is larger than the complete
histogram space whenever the displayed elementary parameter inequality holds. -/
theorem uniformCubic_histogram_cardinality_bound
    {n latentBits : Nat}
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    (2 ^ uniformCubicCoordinateLog n latentBits) ^
        ((uniformCubicDegree n + 1) ^
          Fintype.card (UniformCubicJointScope n latentBits)) <
      2 ^ (2 ^ uniformCubicBlockCount n) := by
  have hExponent :
      uniformCubicCoordinateLog n latentBits *
          ((uniformCubicDegree n + 1) ^
            Fintype.card (UniformCubicJointScope n latentBits)) <
        2 ^ uniformCubicBlockCount n := by
    calc
      uniformCubicCoordinateLog n latentBits *
          ((uniformCubicDegree n + 1) ^
            Fintype.card (UniformCubicJointScope n latentBits)) ≤
          2 ^ uniformCubicCoordinateLogLog n latentBits *
            2 ^ uniformCubicProfileLog n latentBits :=
        Nat.mul_le_mul
          (uniformCubicCoordinateLog_le_two_pow n latentBits)
          (uniformCubicProfileCount_le_two_pow n latentBits)
      _ = 2 ^ (uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits) := by rw [pow_add]
      _ < 2 ^ uniformCubicBlockCount n :=
        Nat.pow_lt_pow_right (by omega) hParameter
  calc
    (2 ^ uniformCubicCoordinateLog n latentBits) ^
        ((uniformCubicDegree n + 1) ^
          Fintype.card (UniformCubicJointScope n latentBits)) =
        2 ^ (uniformCubicCoordinateLog n latentBits *
          ((uniformCubicDegree n + 1) ^
            Fintype.card (UniformCubicJointScope n latentBits))) := by
      rw [pow_mul]
    _ < 2 ^ (2 ^ uniformCubicBlockCount n) :=
      Nat.pow_lt_pow_right (by omega) hExponent

theorem uniformCubic_histogram_cardinality_bound_upTo
    {budget latentBits : Nat} (hLatent : latentBits ≤ budget) :
    (2 ^ uniformCubicCoordinateLog (uniformCubicVisibleBits budget) latentBits) ^
        ((uniformCubicDegree (uniformCubicVisibleBits budget) + 1) ^
          Fintype.card
            (UniformCubicJointScope
              (uniformCubicVisibleBits budget) latentBits)) <
      2 ^ (2 ^ uniformCubicBlockCount (uniformCubicVisibleBits budget)) :=
  uniformCubic_histogram_cardinality_bound
    (uniformCubic_parameter_inequality hLatent)

/-! ## Binary-digit candidate monomials -/

abbrev UniformCubicCandidate (n : Nat) :=
  Fin (uniformCubicBlockCount n) → Fin 2

theorem uniformCubicCandidate_card (n : Nat) :
    Fintype.card (UniformCubicCandidate n) =
      2 ^ uniformCubicBlockCount n := by
  simp [UniformCubicCandidate]

/-- Split a homogeneous tuple index into a visible block and one of its two
binary slots. -/
def uniformCubicIndexEquiv (n : Nat) :
    Fin (uniformCubicBlockCount n) × Fin 2 ≃
      Fin (uniformCubicDegree n) :=
  finProdFinEquiv

/-- All visible cells except the final little-endian binary state. -/
def uniformCubicBlockState
    (n : Nat) (block : Fin (uniformCubicBlockCount n)) : BitVec n :=
  binaryAssignment n block.val

/-- The final visible cell, reserved as a weight-one tuple filler. -/
def uniformCubicFillerState (n : Nat) : BitVec n :=
  binaryAssignment n (uniformCubicBlockCount n)

theorem uniformCubicBlockState_ne_filler
    (n : Nat) (block : Fin (uniformCubicBlockCount n)) :
    uniformCubicBlockState n block ≠ uniformCubicFillerState n := by
  intro hEqual
  have hValues := congrArg binaryAssignmentValue hEqual
  have hBlockLt : block.val < 2 ^ n :=
    lt_trans block.isLt (uniformCubicBlockCount_lt_two_pow n)
  rw [uniformCubicBlockState,
    binaryAssignmentValue_binaryAssignment_of_lt hBlockLt,
    uniformCubicFillerState,
    binaryAssignmentValue_binaryAssignment_of_lt
      (uniformCubicBlockCount_lt_two_pow n)] at hValues
  omega

/-- Digit zero uses two fillers; digit one replaces the first slot by its
block state. -/
def uniformCubicCandidateTuple
    (n : Nat) (candidate : UniformCubicCandidate n) :
    Fin (uniformCubicDegree n) → BitVec n :=
  fun index =>
    let blockSlot := (uniformCubicIndexEquiv n).symm index
    if blockSlot.2 < candidate blockSlot.1 then
      uniformCubicBlockState n blockSlot.1
    else uniformCubicFillerState n

@[simp]
theorem uniformCubicCandidateTuple_index
    (n : Nat) (candidate : UniformCubicCandidate n)
    (block : Fin (uniformCubicBlockCount n)) (slot : Fin 2) :
    uniformCubicCandidateTuple n candidate
        (uniformCubicIndexEquiv n (block, slot)) =
      if slot < candidate block then uniformCubicBlockState n block
      else uniformCubicFillerState n := by
  simp [uniformCubicCandidateTuple]

/-- Binary code of a candidate digit vector. -/
def uniformCubicCandidateCode
    {n : Nat} (candidate : UniformCubicCandidate n) : Nat :=
  ∑ block : Fin (uniformCubicBlockCount n),
    (candidate block).val * 2 ^ block.val

theorem uniformCubicCandidateCode_eq_ofDigits
    {n : Nat} (candidate : UniformCubicCandidate n) :
    uniformCubicCandidateCode candidate =
      Nat.ofDigits 2
        (List.ofFn fun block : Fin (uniformCubicBlockCount n) =>
          (candidate block).val) := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  rfl

theorem uniformCubicCandidateCode_injective (n : Nat) :
    Function.Injective
      (uniformCubicCandidateCode : UniformCubicCandidate n → Nat) := by
  intro left right hCode
  rw [uniformCubicCandidateCode_eq_ofDigits,
    uniformCubicCandidateCode_eq_ofDigits] at hCode
  have hDigits := Nat.ofDigits_inj_of_len_eq
    (b := 2) (by norm_num)
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
      (fun index : Fin (uniformCubicBlockCount n) => (left index).val) =
        fun index : Fin (uniformCubicBlockCount n) => (right index).val :=
    List.ofFn_inj.mp hDigits
  funext index
  exact Fin.ext (congrFun hValues index)

/-- Exponent table defining the eventual rational distribution. -/
def uniformCubicCellExponent (n : Nat) (visible : BitVec n) : Nat :=
  if visible = uniformCubicFillerState n then 0
  else 2 ^ binaryAssignmentValue visible

@[simp]
theorem uniformCubicCellExponent_filler (n : Nat) :
    uniformCubicCellExponent n (uniformCubicFillerState n) = 0 := by
  simp [uniformCubicCellExponent]

@[simp]
theorem uniformCubicCellExponent_block
    (n : Nat) (block : Fin (uniformCubicBlockCount n)) :
    uniformCubicCellExponent n (uniformCubicBlockState n block) =
      2 ^ block.val := by
  rw [uniformCubicCellExponent,
    if_neg (uniformCubicBlockState_ne_filler n block)]
  rw [uniformCubicBlockState,
    binaryAssignmentValue_binaryAssignment_of_lt
      (lt_trans block.isLt (uniformCubicBlockCount_lt_two_pow n))]

theorem sum_uniformCubicCellExponent_candidateTuple
    (n : Nat) (candidate : UniformCubicCandidate n) :
    (∑ index : Fin (uniformCubicDegree n),
      uniformCubicCellExponent n
        (uniformCubicCandidateTuple n candidate index)) =
      uniformCubicCandidateCode candidate := by
  rw [← (uniformCubicIndexEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  unfold uniformCubicCandidateCode
  apply Finset.sum_congr rfl
  intro block _
  simp only [uniformCubicCandidateTuple_index, apply_ite,
    uniformCubicCellExponent_block, uniformCubicCellExponent_filler]
  calc
    (∑ slot : Fin 2,
        if slot < candidate block then 2 ^ block.val else 0) =
        ∑ slot ∈ Finset.Iio (candidate block), 2 ^ block.val := by
      rw [← Finset.sum_filter]
      have hFilter :
          (Finset.univ.filter fun slot : Fin 2 => slot < candidate block) =
            Finset.Iio (candidate block) := by
        ext slot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_Iio (x := slot) (a := candidate block)).symm
      rw [hFilter]
    _ = (candidate block).val * 2 ^ block.val := by
      rw [Finset.sum_const, Fin.card_Iio]
      rfl

/-! ## Parameterized expanded cubic-profile histograms -/

/-- Natural-valued cubic profile of a joint tuple. -/
def uniformCubicNatProfile
    (n latentBits : Nat)
    (tuple : Fin (uniformCubicDegree n) →
      Assignment (Sum (Fin n) (Fin latentBits))) :
    UniformCubicJointScope n latentBits →
      Fin (uniformCubicDegree n + 1) :=
  fun scope =>
    ⟨((Finset.univ : Finset (Fin (uniformCubicDegree n))).filter
      fun index => scope.1 ⊆ trueCoordinates (tuple index)).card,
      Nat.lt_succ_of_le (by
        have hCard := Finset.card_filter_le
          (Finset.univ : Finset (Fin (uniformCubicDegree n)))
          (fun index => scope.1 ⊆ trueCoordinates (tuple index))
        simpa only [Finset.card_univ, Fintype.card_fin] using hCard)⟩

abbrev UniformCubicNatProfile (n latentBits : Nat) :=
  UniformCubicJointScope n latentBits → Fin (uniformCubicDegree n + 1)

def uniformCubicProfileToRat
    {n latentBits : Nat}
    (profile : UniformCubicNatProfile n latentBits) :
    UniformCubicJointScope n latentBits → ℚ :=
  fun scope => profile scope

theorem tupleFeatureProfile_eq_uniformCubicProfileToRat
    (n latentBits : Nat)
    (tuple : Fin (uniformCubicDegree n) →
      Assignment (Sum (Fin n) (Fin latentBits))) :
    tupleFeatureProfile 3 (uniformCubicDegree n) tuple =
      uniformCubicProfileToRat (uniformCubicNatProfile n latentBits tuple) := by
  funext scope
  let predicate : Fin (uniformCubicDegree n) → Prop := fun index =>
    scope.1 ⊆ trueCoordinates (tuple index)
  have hCard := Finset.card_filter predicate
    (Finset.univ : Finset (Fin (uniformCubicDegree n)))
  have hCast := congrArg (fun value : Nat => (value : ℚ)) hCard
  simpa only [tupleFeatureProfile, uniformCubicProfileToRat,
    uniformCubicNatProfile, rationalMonomialValue, predicate,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_const_zero, Finset.sum_filter] using hCast.symm

theorem uniformCubicNatProfile_card (n latentBits : Nat) :
    Fintype.card (UniformCubicNatProfile n latentBits) =
      (uniformCubicDegree n + 1) ^
        Fintype.card (UniformCubicJointScope n latentBits) := by
  simp [UniformCubicNatProfile]

abbrev UniformCubicLatentLabeling (n latentBits : Nat) :=
  Fin (uniformCubicDegree n) → Assignment (Fin latentBits)

theorem uniformCubicLatentLabeling_card (n latentBits : Nat) :
    Fintype.card (UniformCubicLatentLabeling n latentBits) =
      2 ^ (latentBits * uniformCubicDegree n) := by
  simp only [UniformCubicLatentLabeling, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  exact (pow_mul 2 latentBits (uniformCubicDegree n)).symm

/-- Multiset of profiles obtained from a candidate subset after expanding
every factor over every latent assignment. -/
noncomputable def uniformCubicExpansion
    (n latentBits : Nat)
    (candidates : Finset (UniformCubicCandidate n)) :
    Multiset (UniformCubicNatProfile n latentBits) :=
  ((Finset.univ : Finset
      (candidates × UniformCubicLatentLabeling n latentBits))).val.map
    (fun expanded =>
      uniformCubicNatProfile n latentBits
        (liftTuple
          (uniformCubicCandidateTuple n expanded.1.1) expanded.2))

theorem uniformCubicExpansion_card
    (n latentBits : Nat)
    (candidates : Finset (UniformCubicCandidate n)) :
    (uniformCubicExpansion n latentBits candidates).card =
      candidates.card * 2 ^ (latentBits * uniformCubicDegree n) := by
  simp only [uniformCubicExpansion, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
    uniformCubicLatentLabeling_card]

abbrev UniformCubicHistogramCoordinate (n latentBits : Nat) :=
  Fin (2 ^ uniformCubicCoordinateLog n latentBits)

abbrev UniformCubicHistogram (n latentBits : Nat) :=
  UniformCubicNatProfile n latentBits →
    UniformCubicHistogramCoordinate n latentBits

noncomputable def uniformCubicHistogram
    (n latentBits : Nat)
    (candidates : Finset (UniformCubicCandidate n)) :
    UniformCubicHistogram n latentBits :=
  fun profile =>
    ⟨(uniformCubicExpansion n latentBits candidates).count profile, by
      calc
        (uniformCubicExpansion n latentBits candidates).count profile ≤
            (uniformCubicExpansion n latentBits candidates).card :=
          Multiset.count_le_card _ _
        _ = candidates.card *
            2 ^ (latentBits * uniformCubicDegree n) :=
          uniformCubicExpansion_card n latentBits candidates
        _ ≤ (2 ^ uniformCubicBlockCount n) *
            2 ^ (latentBits * uniformCubicDegree n) := by
          apply Nat.mul_le_mul_right
          simpa only [uniformCubicCandidate_card] using
            candidates.card_le_univ
        _ = 2 ^ (uniformCubicBlockCount n +
            latentBits * uniformCubicDegree n) := by rw [pow_add]
        _ < 2 ^ uniformCubicCoordinateLog n latentBits := by
          unfold uniformCubicCoordinateLog
          exact Nat.pow_lt_pow_right (by omega) (by omega)⟩

theorem uniformCubicHistogram_card (n latentBits : Nat) :
    Fintype.card (UniformCubicHistogram n latentBits) =
      (2 ^ uniformCubicCoordinateLog n latentBits) ^
        ((uniformCubicDegree n + 1) ^
          Fintype.card (UniformCubicJointScope n latentBits)) := by
  calc
    Fintype.card (UniformCubicHistogram n latentBits) =
        Fintype.card (UniformCubicHistogramCoordinate n latentBits) ^
          Fintype.card (UniformCubicNatProfile n latentBits) :=
      Fintype.card_fun
    _ = (2 ^ uniformCubicCoordinateLog n latentBits) ^
        ((uniformCubicDegree n + 1) ^
          Fintype.card (UniformCubicJointScope n latentBits)) := by
      rw [Fintype.card_fin, uniformCubicNatProfile_card]

/-- Finite pigeonhole collision for arbitrary parameters satisfying the
elementary count inequality. -/
theorem exists_uniformCubicExpansion_collision
    {n latentBits : Nat}
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    ∃ left right : Finset (UniformCubicCandidate n),
      left ≠ right ∧
        uniformCubicExpansion n latentBits left =
          uniformCubicExpansion n latentBits right := by
  classical
  have hCard : Fintype.card (UniformCubicHistogram n latentBits) <
      Fintype.card (Finset (UniformCubicCandidate n)) := by
    rw [uniformCubicHistogram_card, Fintype.card_finset,
      uniformCubicCandidate_card]
    exact uniformCubic_histogram_cardinality_bound hParameter
  have hNotInjective :
      ¬Function.Injective (uniformCubicHistogram n latentBits) :=
    Fintype.not_injective_of_card_lt
      (uniformCubicHistogram n latentBits) hCard
  simp only [Function.Injective] at hNotInjective
  push_neg at hNotInjective
  rcases hNotInjective with
    ⟨left, right, hHistogram, hDistinct⟩
  refine ⟨left, right, hDistinct, ?_⟩
  apply Multiset.ext.mpr
  intro profile
  have hCoordinate := congrFun hHistogram profile
  have hValue := congrArg Fin.val hCoordinate
  simpa only [uniformCubicHistogram] using hValue

theorem uniformCubicExpansion_collision_card_eq
    {n latentBits : Nat}
    {left right : Finset (UniformCubicCandidate n)}
    (hExpansion : uniformCubicExpansion n latentBits left =
      uniformCubicExpansion n latentBits right) :
    left.card = right.card := by
  have hCard := congrArg Multiset.card hExpansion
  rw [uniformCubicExpansion_card, uniformCubicExpansion_card] at hCard
  exact Nat.mul_right_cancel (by positivity) hCard

/-! ## Compiling a collision into a marginal-trade certificate -/

theorem enumeratedProfileMultiset_eq_uniformCubicExpansion
    {n latentBits termCount : Nat}
    (candidates : Finset (UniformCubicCandidate n))
    (enumeration : Fin termCount ≃ candidates) :
    ((Finset.univ : Finset
        (Fin termCount × UniformCubicLatentLabeling n latentBits)).val.map
      (fun expanded => tupleFeatureProfile 3 (uniformCubicDegree n)
        (liftTuple
          (uniformCubicCandidateTuple n (enumeration expanded.1).1)
          expanded.2))) =
      (uniformCubicExpansion n latentBits candidates).map
        uniformCubicProfileToRat := by
  classical
  simp_rw [tupleFeatureProfile_eq_uniformCubicProfileToRat]
  unfold uniformCubicExpansion
  rw [Multiset.map_map]
  let pairEquivalence :
      (Fin termCount × UniformCubicLatentLabeling n latentBits) ≃
        (candidates × UniformCubicLatentLabeling n latentBits) :=
    Equiv.prodCongr enumeration (Equiv.refl _)
  let profileFunction :
      candidates × UniformCubicLatentLabeling n latentBits →
        (UniformCubicJointScope n latentBits → ℚ) :=
    fun expanded => uniformCubicProfileToRat
      (uniformCubicNatProfile n latentBits
        (liftTuple
          (uniformCubicCandidateTuple n expanded.1.1) expanded.2))
  simpa only [pairEquivalence, profileFunction, Function.comp_apply]
    using univ_val_map_comp_equiv pairEquivalence profileFunction

structure UniformCubicExpansionCollision (n latentBits : Nat) where
  left : Finset (UniformCubicCandidate n)
  right : Finset (UniformCubicCandidate n)
  distinct : left ≠ right
  expansion_eq : uniformCubicExpansion n latentBits left =
    uniformCubicExpansion n latentBits right
  card_eq : left.card = right.card

noncomputable def uniformCubicChosenCollision
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    UniformCubicExpansionCollision n latentBits :=
  { left := (exists_uniformCubicExpansion_collision hParameter).choose
    right :=
      (exists_uniformCubicExpansion_collision hParameter).choose_spec.choose
    distinct :=
      (exists_uniformCubicExpansion_collision hParameter).choose_spec.choose_spec.1
    expansion_eq :=
      (exists_uniformCubicExpansion_collision hParameter).choose_spec.choose_spec.2
    card_eq := uniformCubicExpansion_collision_card_eq
      (exists_uniformCubicExpansion_collision hParameter).choose_spec.choose_spec.2 }

noncomputable abbrev uniformCubicTermCount
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) : Nat :=
  (uniformCubicChosenCollision n latentBits hParameter).left.card

noncomputable def uniformCubicPositiveEnumeration
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    Fin (uniformCubicTermCount n latentBits hParameter) ≃
      (uniformCubicChosenCollision n latentBits hParameter).left :=
  (uniformCubicChosenCollision n latentBits hParameter).left.equivFin.symm

noncomputable def uniformCubicNegativeEnumeration
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    Fin (uniformCubicTermCount n latentBits hParameter) ≃
      (uniformCubicChosenCollision n latentBits hParameter).right :=
  (finCongr
      (uniformCubicChosenCollision n latentBits hParameter).card_eq).trans
    (uniformCubicChosenCollision n latentBits hParameter).right.equivFin.symm

/-- Boundary-safe cubic marginal trade against exactly `latentBits` hidden
bits. -/
noncomputable def uniformCubicCertificate
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    MarginalTradeCertificate 3 (uniformCubicDegree n)
      (uniformCubicTermCount n latentBits hParameter)
      (Fin n) (Fin latentBits) where
  positive := fun term =>
    uniformCubicCandidateTuple n
      (uniformCubicPositiveEnumeration n latentBits hParameter term).1
  negative := fun term =>
    uniformCubicCandidateTuple n
      (uniformCubicNegativeEnumeration n latentBits hParameter term).1
  profileBalance := by
    rw [enumeratedProfileMultiset_eq_uniformCubicExpansion
      (uniformCubicChosenCollision n latentBits hParameter).left
      (uniformCubicPositiveEnumeration n latentBits hParameter)]
    rw [enumeratedProfileMultiset_eq_uniformCubicExpansion
      (uniformCubicChosenCollision n latentBits hParameter).right
      (uniformCubicNegativeEnumeration n latentBits hParameter)]
    rw [(uniformCubicChosenCollision n latentBits hParameter).expansion_eq]

/-! ## The parameterized explicit rational distribution -/

def uniformCubicUnnormalizedRat
    (n : Nat) (visible : BitVec n) : ℚ :=
  2 ^ uniformCubicCellExponent n visible

noncomputable def uniformCubicNormalizerRat (n : Nat) : ℚ :=
  ∑ visible : BitVec n, uniformCubicUnnormalizedRat n visible

theorem uniformCubicUnnormalizedRat_pos
    (n : Nat) (visible : BitVec n) :
    0 < uniformCubicUnnormalizedRat n visible := by
  unfold uniformCubicUnnormalizedRat
  exact pow_pos (by norm_num) _

theorem uniformCubicNormalizerRat_pos (n : Nat) :
    0 < uniformCubicNormalizerRat n := by
  classical
  unfold uniformCubicNormalizerRat
  exact Finset.sum_pos
    (fun visible _ => uniformCubicUnnormalizedRat_pos n visible)
    Finset.univ_nonempty

noncomputable def uniformCubicWeightsRat
    (n : Nat) (visible : BitVec n) : ℚ :=
  uniformCubicUnnormalizedRat n visible / uniformCubicNormalizerRat n

theorem uniformCubicWeightsRat_pos
    (n : Nat) (visible : BitVec n) :
    0 < uniformCubicWeightsRat n visible :=
  div_pos (uniformCubicUnnormalizedRat_pos n visible)
    (uniformCubicNormalizerRat_pos n)

theorem sum_uniformCubicWeightsRat (n : Nat) :
    (∑ visible : BitVec n, uniformCubicWeightsRat n visible) = 1 := by
  classical
  unfold uniformCubicWeightsRat uniformCubicNormalizerRat
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos
    (fun visible _ => uniformCubicUnnormalizedRat_pos n visible)
    Finset.univ_nonempty))

noncomputable def uniformCubicWeights
    (n : Nat) (visible : BitVec n) : ℝ :=
  uniformCubicWeightsRat n visible

/-- Explicit full-support rational law on `n` visible bits. -/
noncomputable def uniformCubicDistribution (n : Nat) :
    Distribution (BitVec n) :=
  distributionOfRealWeights (uniformCubicWeights n)
    (fun visible => Rat.cast_nonneg.mpr
      (uniformCubicWeightsRat_pos n visible).le)
    (by
      have hCast := congrArg (fun value : ℚ => (value : ℝ))
        (sum_uniformCubicWeightsRat n)
      simpa [uniformCubicWeights, Rat.cast_sum] using hCast)

@[simp]
theorem uniformCubicDistribution_apply_toReal
    (n : Nat) (visible : BitVec n) :
    (uniformCubicDistribution n visible).toReal =
      uniformCubicWeights n visible := by
  exact distributionOfRealWeights_apply_toReal _ _ _ visible

theorem uniformCubicDistribution_support (n : Nat) :
    (uniformCubicDistribution n).support = Set.univ := by
  ext visible
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff (uniformCubicDistribution n) visible).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [uniformCubicDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  have hPositive : 0 < uniformCubicWeights n visible :=
    Rat.cast_pos.mpr (uniformCubicWeightsRat_pos n visible)
  exact (ne_of_gt hPositive) hReal

/-! ## Detection of every chosen collision -/

theorem prod_uniformCubicUnnormalizedRat_candidateTuple
    (n : Nat) (candidate : UniformCubicCandidate n) :
    (∏ index : Fin (uniformCubicDegree n),
      uniformCubicUnnormalizedRat n
        (uniformCubicCandidateTuple n candidate index)) =
      (2 : ℚ) ^ uniformCubicCandidateCode candidate := by
  unfold uniformCubicUnnormalizedRat
  rw [Finset.prod_pow_eq_pow_sum]
  rw [sum_uniformCubicCellExponent_candidateTuple]

theorem prod_uniformCubicWeightsRat_candidateTuple
    (n : Nat) (candidate : UniformCubicCandidate n) :
    (∏ index : Fin (uniformCubicDegree n),
      uniformCubicWeightsRat n
        (uniformCubicCandidateTuple n candidate index)) =
      (2 : ℚ) ^ uniformCubicCandidateCode candidate /
        uniformCubicNormalizerRat n ^ uniformCubicDegree n := by
  unfold uniformCubicWeightsRat
  rw [Finset.prod_div_distrib]
  rw [prod_uniformCubicUnnormalizedRat_candidateTuple]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def uniformCubicCandidatePowerSum
    {n : Nat} (candidates : Finset (UniformCubicCandidate n)) : Nat :=
  ∑ candidate ∈ candidates,
    2 ^ uniformCubicCandidateCode candidate

theorem uniformCubicCandidatePowerSum_injective (n : Nat) :
    Function.Injective
      (uniformCubicCandidatePowerSum :
        Finset (UniformCubicCandidate n) → Nat) := by
  classical
  intro left right hSums
  apply Finset.image_injective (uniformCubicCandidateCode_injective n)
  apply Finset.geomSum_injective (n := 2) (by omega)
  have hLeft :
      (∑ code ∈ left.image uniformCubicCandidateCode, 2 ^ code) =
        uniformCubicCandidatePowerSum left := by
    rw [Finset.sum_image
      (uniformCubicCandidateCode_injective n).injOn]
    rfl
  have hRight :
      (∑ code ∈ right.image uniformCubicCandidateCode, 2 ^ code) =
        uniformCubicCandidatePowerSum right := by
    rw [Finset.sum_image
      (uniformCubicCandidateCode_injective n).injOn]
    rfl
  change
    (∑ code ∈ left.image uniformCubicCandidateCode, 2 ^ code) =
      ∑ code ∈ right.image uniformCubicCandidateCode, 2 ^ code
  exact hLeft.trans (hSums.trans hRight.symm)

theorem sum_prod_uniformCubicWeights_of_equiv
    {n termCount : Nat}
    (candidates : Finset (UniformCubicCandidate n))
    (enumeration : Fin termCount ≃ candidates) :
    (∑ term : Fin termCount,
      ∏ index : Fin (uniformCubicDegree n),
        uniformCubicWeights n
          (uniformCubicCandidateTuple n (enumeration term).1 index)) =
      (uniformCubicCandidatePowerSum candidates : ℝ) /
        (uniformCubicNormalizerRat n : ℝ) ^ uniformCubicDegree n := by
  classical
  calc
    (∑ term : Fin termCount,
        ∏ index : Fin (uniformCubicDegree n),
          uniformCubicWeights n
            (uniformCubicCandidateTuple n (enumeration term).1 index)) =
        ∑ candidate : candidates,
          ∏ index : Fin (uniformCubicDegree n),
            uniformCubicWeights n
              (uniformCubicCandidateTuple n candidate.1 index) := by
      exact enumeration.sum_comp (fun candidate : candidates =>
        ∏ index : Fin (uniformCubicDegree n),
          uniformCubicWeights n
            (uniformCubicCandidateTuple n candidate.1 index))
    _ = (uniformCubicCandidatePowerSum candidates : ℝ) /
          (uniformCubicNormalizerRat n : ℝ) ^ uniformCubicDegree n := by
      rw [show
        (∑ candidate : candidates,
          ∏ index : Fin (uniformCubicDegree n),
            uniformCubicWeights n
              (uniformCubicCandidateTuple n candidate.1 index)) =
        ∑ candidate ∈ candidates,
          ∏ index : Fin (uniformCubicDegree n),
            uniformCubicWeights n
              (uniformCubicCandidateTuple n candidate index) from
        Finset.sum_coe_sort candidates (fun candidate =>
          ∏ index : Fin (uniformCubicDegree n),
            uniformCubicWeights n
              (uniformCubicCandidateTuple n candidate index))]
      simp_rw [uniformCubicWeights]
      simp_rw [← Rat.cast_prod]
      simp_rw [prod_uniformCubicWeightsRat_candidateTuple]
      simp_rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
      rw [← Finset.sum_div]
      congr 1
      norm_cast

theorem uniformCubicCertificate_positiveValue
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    (uniformCubicCertificate n latentBits hParameter).positiveValue
        (uniformCubicWeights n) =
      (uniformCubicCandidatePowerSum
          (uniformCubicChosenCollision n latentBits hParameter).left : ℝ) /
        (uniformCubicNormalizerRat n : ℝ) ^ uniformCubicDegree n := by
  simpa [MarginalTradeCertificate.positiveValue,
    uniformCubicCertificate] using
    sum_prod_uniformCubicWeights_of_equiv
      (uniformCubicChosenCollision n latentBits hParameter).left
      (uniformCubicPositiveEnumeration n latentBits hParameter)

theorem uniformCubicCertificate_negativeValue
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    (uniformCubicCertificate n latentBits hParameter).negativeValue
        (uniformCubicWeights n) =
      (uniformCubicCandidatePowerSum
          (uniformCubicChosenCollision n latentBits hParameter).right : ℝ) /
        (uniformCubicNormalizerRat n : ℝ) ^ uniformCubicDegree n := by
  simpa [MarginalTradeCertificate.negativeValue,
    uniformCubicCertificate] using
    sum_prod_uniformCubicWeights_of_equiv
      (uniformCubicChosenCollision n latentBits hParameter).right
      (uniformCubicNegativeEnumeration n latentBits hParameter)

theorem uniformCubicCertificate_detects
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    (uniformCubicCertificate n latentBits hParameter).positiveValue
        (fun visible => (uniformCubicDistribution n visible).toReal) ≠
      (uniformCubicCertificate n latentBits hParameter).negativeValue
        (fun visible => (uniformCubicDistribution n visible).toReal) := by
  simp_rw [uniformCubicDistribution_apply_toReal]
  rw [uniformCubicCertificate_positiveValue,
    uniformCubicCertificate_negativeValue]
  intro hEqual
  have hDenominator :
      (uniformCubicNormalizerRat n : ℝ) ^ uniformCubicDegree n ≠ 0 :=
    pow_ne_zero _ (Rat.cast_ne_zero.mpr
      (ne_of_gt (uniformCubicNormalizerRat_pos n)))
  have hNumerators :
      (uniformCubicCandidatePowerSum
          (uniformCubicChosenCollision n latentBits hParameter).left : ℝ) =
        (uniformCubicCandidatePowerSum
          (uniformCubicChosenCollision n latentBits hParameter).right : ℝ) :=
    (div_left_inj' hDenominator).mp hEqual
  have hNat :
      uniformCubicCandidatePowerSum
          (uniformCubicChosenCollision n latentBits hParameter).left =
        uniformCubicCandidatePowerSum
          (uniformCubicChosenCollision n latentBits hParameter).right := by
    exact_mod_cast hNumerators
  exact (uniformCubicChosenCollision n latentBits hParameter).distinct
    (uniformCubicCandidatePowerSum_injective n hNat)

theorem uniformCubicDistribution_no_localization
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    ¬HasKLocalizationBits 3 latentBits n (uniformCubicDistribution n) :=
  (uniformCubicCertificate n latentBits hParameter).obstructs_localization
    (uniformCubicCertificate_detects n latentBits hParameter)

/-! ## A linear warm-up -/

/-- The budget-indexed member of the explicit family. -/
noncomputable abbrev uniformCubicHardDistribution (budget : Nat) :
    Distribution (BitVec (uniformCubicVisibleBits budget)) :=
  uniformCubicDistribution (uniformCubicVisibleBits budget)

theorem uniformCubicHardDistribution_support (budget : Nat) :
    (uniformCubicHardDistribution budget).support = Set.univ :=
  uniformCubicDistribution_support (uniformCubicVisibleBits budget)

/-- Exact trade-certificate family for every hidden-bit count through the
requested budget. -/
theorem uniformCubicTradeCertificates_upTo (budget : Nat) :
    ∀ latentBits, latentBits ≤ budget →
      ∃ degree termCount,
        ∃ certificate : MarginalTradeCertificate
            3 degree termCount (Fin (uniformCubicVisibleBits budget))
              (Fin latentBits),
          certificate.positiveValue
              (fun visible =>
                (uniformCubicHardDistribution budget visible).toReal) ≠
            certificate.negativeValue
              (fun visible =>
                (uniformCubicHardDistribution budget visible).toReal) := by
  intro latentBits hLatent
  let hParameter := uniformCubic_parameter_inequality hLatent
  exact
    ⟨uniformCubicDegree (uniformCubicVisibleBits budget),
      uniformCubicTermCount
        (uniformCubicVisibleBits budget) latentBits hParameter,
      uniformCubicCertificate
        (uniformCubicVisibleBits budget) latentBits hParameter,
      uniformCubicCertificate_detects
        (uniformCubicVisibleBits budget) latentBits hParameter⟩

/-- For every natural budget there is a concrete full-support rational law
on `budget + 64` visible bits whose cubic localization complexity exceeds
that budget.  In particular, explicit full-support cubic complexity is
unbounded. -/
theorem uniformCubicHardDistribution_localizationComplexity_gt
    (budget : Nat) :
    budget < localizationComplexityBits 3
      (uniformCubicVisibleBits budget)
      (uniformCubicHardDistribution budget) :=
  MarginalTradeCertificate.localizationComplexity_gt_of_tradeCertificates
    (by omega : 2 ≤ 3) (uniformCubicHardDistribution budget)
      (uniformCubicTradeCertificates_upTo budget)

/-- Equivalent visible-dimension form: for every `n ≥ 64`, the directly
`n`-indexed table has cubic localization complexity strictly greater than
`n - 64`. -/
theorem uniformCubicDistribution_localizationComplexity_gt_sub
    (n : Nat) (hn : 64 ≤ n) :
    n - 64 < localizationComplexityBits 3 n
      (uniformCubicDistribution n) := by
  have hDimension : uniformCubicVisibleBits (n - 64) = n := by
    unfold uniformCubicVisibleBits
    omega
  apply MarginalTradeCertificate.localizationComplexity_gt_of_tradeCertificates
    (by omega : 2 ≤ 3) (uniformCubicDistribution n)
  intro latentBits hLatent
  have hParameter :=
    uniformCubic_parameter_inequality
      (budget := n - 64) (latentBits := latentBits) hLatent
  rw [hDimension] at hParameter
  exact
    ⟨uniformCubicDegree n,
      uniformCubicTermCount n latentBits hParameter,
      uniformCubicCertificate n latentBits hParameter,
      uniformCubicCertificate_detects n latentBits hParameter⟩

/-! ## An exponential specialization -/

/-- Visible dimension of the superlinear family. -/
def superlinearCubicVisibleBits (scale : Nat) : Nat :=
  24 + 4 * scale

/-- Hidden-bit budget ruled out at scale `scale`. -/
def superlinearCubicBudget (scale : Nat) : Nat :=
  2 ^ scale

/-- A deliberately simple envelope for every linear term occurring in the
cubic profile count. -/
theorem superlinearCubic_linear_envelope (scale : Nat) :
    superlinearCubicVisibleBits scale + superlinearCubicBudget scale + 3 ≤
      2 ^ (scale + 5) := by
  let power := 2 ^ scale
  have hOne : 1 ≤ power := by
    have hPositive : 0 < power := by
      dsimp [power]
      positivity
    omega
  have hScale : scale ≤ power := by
    exact scale.lt_two_pow_self.le
  have hConstant : 27 ≤ 27 * power := by
    simpa only [mul_one] using Nat.mul_le_mul_left 27 hOne
  have hLinear : 4 * scale ≤ 4 * power :=
    Nat.mul_le_mul_left 4 hScale
  calc
    superlinearCubicVisibleBits scale +
        superlinearCubicBudget scale + 3 =
        27 + 4 * scale + power := by
      simp [superlinearCubicVisibleBits, superlinearCubicBudget, power]
      omega
    _ ≤ 27 * power + 4 * power + power :=
      Nat.add_le_add (Nat.add_le_add hConstant hLinear) le_rfl
    _ = 32 * power := by omega
    _ = 2 ^ 5 * 2 ^ scale := by
      dsimp [power]
    _ = 2 ^ (5 + scale) := (pow_add 2 5 scale).symm
    _ = 2 ^ (scale + 5) := by
      congr 1
      omega

/-- The generic finite-profile pigeonhole inequality holds for an exponential
hidden budget on only four times as many visible bits (up to an additive
constant). -/
theorem superlinearCubic_parameter_inequality
    {scale latentBits : Nat}
    (hLatent : latentBits ≤ superlinearCubicBudget scale) :
    uniformCubicCoordinateLogLog
          (superlinearCubicVisibleBits scale) latentBits +
        uniformCubicProfileLog
          (superlinearCubicVisibleBits scale) latentBits <
      uniformCubicBlockCount (superlinearCubicVisibleBits scale) := by
  let n := superlinearCubicVisibleBits scale
  let budget := superlinearCubicBudget scale
  let envelope := 2 ^ (scale + 5)
  let profileEnvelope := 2 ^ (4 * scale + 20)
  have hEnvelopeBase : n + budget + 3 ≤ envelope := by
    exact superlinearCubic_linear_envelope scale
  have hCoordinate : n + latentBits + 3 ≤ envelope := by
    exact le_trans (by omega) hEnvelopeBase
  have hInside : n + latentBits + 1 ≤ envelope := by
    omega
  have hVisible : n + 1 ≤ envelope := by
    omega
  have hProfile :
      uniformCubicProfileLog n latentBits ≤ profileEnvelope := by
    unfold uniformCubicProfileLog
    calc
      (n + 1) * (n + latentBits + 1) ^ 3 ≤
          envelope * envelope ^ 3 :=
        Nat.mul_le_mul hVisible (Nat.pow_le_pow_left hInside 3)
      _ = envelope ^ 3 * envelope := Nat.mul_comm _ _
      _ = envelope ^ 4 := (pow_succ envelope 3).symm
      _ = 2 ^ ((scale + 5) * 4) := by
        exact (pow_mul 2 (scale + 5) 4).symm
      _ = profileEnvelope := by
        dsimp [profileEnvelope]
        congr 1
        omega
  have hCoordinateProfile :
      uniformCubicCoordinateLogLog n latentBits ≤ profileEnvelope := by
    unfold uniformCubicCoordinateLogLog
    have hEnvelopeLe : envelope ≤ profileEnvelope := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans hCoordinate hEnvelopeLe
  have hProfilePositive : 0 < profileEnvelope := by positivity
  have hTotal :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits + 1 <
        4 * profileEnvelope := by
    omega
  have hFourProfile :
      4 * profileEnvelope = 2 ^ (4 * scale + 22) := by
    calc
      4 * profileEnvelope = 2 ^ 2 * 2 ^ (4 * scale + 20) := by
        rfl
      _ = 2 ^ (2 + (4 * scale + 20)) :=
        (pow_add 2 2 (4 * scale + 20)).symm
      _ = 2 ^ (4 * scale + 22) := by
        congr 1
        omega
  have hExponent : 4 * scale + 22 < n := by
    dsimp [n, superlinearCubicVisibleBits]
    omega
  have hSucc :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits + 1 < 2 ^ n := by
    calc
      _ < 4 * profileEnvelope := hTotal
      _ = 2 ^ (4 * scale + 22) := hFourProfile
      _ < 2 ^ n := Nat.pow_lt_pow_right (by omega) hExponent
  have hPowerPositive : 0 < 2 ^ n := by positivity
  unfold uniformCubicBlockCount
  change uniformCubicCoordinateLogLog n latentBits +
      uniformCubicProfileLog n latentBits < 2 ^ n - 1
  omega

/-- The scale-indexed explicit full-support rational distribution. -/
noncomputable abbrev superlinearCubicDistribution (scale : Nat) :
    Distribution (BitVec (superlinearCubicVisibleBits scale)) :=
  uniformCubicDistribution (superlinearCubicVisibleBits scale)

theorem superlinearCubicDistribution_support (scale : Nat) :
    (superlinearCubicDistribution scale).support = Set.univ :=
  uniformCubicDistribution_support (superlinearCubicVisibleBits scale)

/-- Main superlinear result: on `4m+24` visible bits, the explicit
full-support rational law requires more than `2^m` hidden bits in every cubic
localization. -/
theorem superlinearCubicDistribution_localizationComplexity_gt
    (scale : Nat) :
    2 ^ scale < localizationComplexityBits 3
      (superlinearCubicVisibleBits scale)
      (superlinearCubicDistribution scale) := by
  apply MarginalTradeCertificate.localizationComplexity_gt_of_tradeCertificates
    (by omega : 2 ≤ 3) (superlinearCubicDistribution scale)
  intro latentBits hLatent
  have hParameter :=
    superlinearCubic_parameter_inequality hLatent
  exact
    ⟨uniformCubicDegree (superlinearCubicVisibleBits scale),
      uniformCubicTermCount
        (superlinearCubicVisibleBits scale) latentBits hParameter,
      uniformCubicCertificate
        (superlinearCubicVisibleBits scale) latentBits hParameter,
      uniformCubicCertificate_detects
        (superlinearCubicVisibleBits scale) latentBits hParameter⟩

theorem superlinearCubicVisibleBits_sq_succ_le_double (scale : Nat) :
    superlinearCubicVisibleBits (scale + 1) ^ 2 ≤
      2 * superlinearCubicVisibleBits scale ^ 2 := by
  simp only [superlinearCubicVisibleBits, pow_two]
  nlinarith [sq_nonneg scale]

/-- From scale thirteen onward, the exponential budget is already larger
than the square of the visible dimension. -/
theorem superlinearCubicVisibleBits_sq_lt_budget
    (scale : Nat) (hScale : 13 ≤ scale) :
    superlinearCubicVisibleBits scale ^ 2 < 2 ^ scale := by
  induction scale, hScale using Nat.le_induction with
  | base => norm_num [superlinearCubicVisibleBits]
  | succ scale hScale ih =>
      calc
        superlinearCubicVisibleBits (scale + 1) ^ 2 ≤
            superlinearCubicVisibleBits scale ^ 2 +
              superlinearCubicVisibleBits scale ^ 2 := by
          simpa [two_mul] using
            superlinearCubicVisibleBits_sq_succ_le_double scale
        _ < 2 ^ scale + 2 ^ scale := Nat.add_lt_add ih ih
        _ = 2 ^ (scale + 1) := (Nat.two_pow_succ scale).symm

/-- A literal superlinear corollary: for every `scale ≥ 13`, the cubic
localization complexity of the explicit full-support law is greater than the
square of its number of visible bits. -/
theorem superlinearCubicDistribution_localizationComplexity_gt_sq
    (scale : Nat) (hScale : 13 ≤ scale) :
    superlinearCubicVisibleBits scale ^ 2 <
      localizationComplexityBits 3
        (superlinearCubicVisibleBits scale)
        (superlinearCubicDistribution scale) :=
  lt_trans (superlinearCubicVisibleBits_sq_lt_budget scale hScale)
    (superlinearCubicDistribution_localizationComplexity_gt scale)

end KLocality
