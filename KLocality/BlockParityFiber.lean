import KLocality.BinaryAgreementTransform
import KLocality.SelectorTrade
import KLocality.UniformParityLowerBound

namespace KLocality

open scoped BigOperators

/-!
# The four-bit parity block

The structured cubic fiber used in the explicitness investigation is built
from the two parity halves of a four-dimensional Boolean cube.  This file
checks the local facts on which that construction rests: the halves have
eight points, have identical moments through degree three, and their
intersection kernel is the two-by-two agreement matrix with diagonal entry
`2^8 = 256`.
-/

/-- Parity of a four-bit assignment. -/
def parityFour (assignment : BitVec 4) : Bool :=
  xor (xor (assignment 0) (assignment 1))
    (xor (assignment 2) (assignment 3))

/-- One of the two parity halves of the four-cube. -/
def parityFourClass (value : Fin 2) : Finset (BitVec 4) :=
  Finset.univ.filter fun assignment =>
    parityFour assignment = decide (value = 1)

theorem parityFourClass_card (value : Fin 2) :
    (parityFourClass value).card = 8 := by
  fin_cases value <;> decide +kernel

theorem parityFour_flipBit :
    ∀ (coordinate : Fin 4) (assignment : BitVec 4),
      parityFour (flipBit coordinate assignment) = !parityFour assignment := by
  decide +kernel

/-- Even and odd parity have identical Boolean moments of every order at
most three. -/
theorem parityFourClass_cubicMoment_eq :
    ∀ scope : FeatureScope (Fin 4) 3,
      (∑ assignment ∈ parityFourClass 0,
        rationalMonomialValue scope.1 assignment) =
      ∑ assignment ∈ parityFourClass 1,
        rationalMonomialValue scope.1 assignment := by
  decide +kernel

theorem parityFourClass_inter_card (left right : Fin 2) :
    ((parityFourClass left) ∩ parityFourClass right).card =
      if left = right then 8 else 0 := by
  fin_cases left <;> fin_cases right <;> decide +kernel

/-- The Boolean-tilt response of two parity blocks is exactly one coordinate
of the `256`-agreement kernel. -/
theorem two_pow_parityFourClass_inter_card (left right : Fin 2) :
    (2 : ℤ) ^ ((parityFourClass left ∩ parityFourClass right).card) =
      binaryAgreementEntry 256 left right := by
  rw [parityFourClass_inter_card]
  by_cases hEqual : left = right
  · simp [hEqual, binaryAgreementEntry]
  · simp [hEqual, binaryAgreementEntry]

/-! ## The full block-parity moment fiber -/

/-- Visible variables for `q` prefix bits, four parity bits, and one marker
bit.  A sum type keeps the three roles definitionally separate. -/
abbrev BlockParityVar (q : Nat) :=
  Sum (Fin q) (Sum (Fin 4) (Fin 1))

/-- Embed one prefix and one parity-block assignment into the visible cube.
The marker bit is always false. -/
def blockParityState {q : Nat}
    (label : BitVec q) (suffix : BitVec 4) :
    Assignment (BlockParityVar q) :=
  fun coordinate =>
    match coordinate with
    | Sum.inl prefixCoordinate => label prefixCoordinate
    | Sum.inr (Sum.inl suffixCoordinate) => suffix suffixCoordinate
    | Sum.inr (Sum.inr _) => false

/-- Flip one coordinate of an assignment over an arbitrary finite variable
type. -/
def flipAssignment
    {Var : Type*} [DecidableEq Var]
    (coordinate : Var) (assignment : Assignment Var) : Assignment Var :=
  fun candidate =>
    if candidate = coordinate then !assignment candidate else assignment candidate

@[simp]
theorem flipAssignment_apply_self
    {Var : Type*} [DecidableEq Var]
    (coordinate : Var) (assignment : Assignment Var) :
    flipAssignment coordinate assignment coordinate = !assignment coordinate := by
  simp [flipAssignment]

theorem flipAssignment_apply_of_ne
    {Var : Type*} [DecidableEq Var]
    {coordinate candidate : Var} (hNe : candidate ≠ coordinate)
    (assignment : Assignment Var) :
    flipAssignment coordinate assignment candidate = assignment candidate := by
  simp [flipAssignment, hNe]

/-- Flipping a coordinate outside a Boolean monomial scope leaves its
rational value unchanged. -/
theorem rationalMonomialValue_flipAssignment_of_not_mem
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (scope : Finset Var) (assignment : Assignment Var)
    (coordinate : Var) (hUnused : coordinate ∉ scope) :
    rationalMonomialValue scope (flipAssignment coordinate assignment) =
      rationalMonomialValue scope assignment := by
  unfold rationalMonomialValue
  congr 1
  apply propext
  constructor
  · intro hSubset candidate hCandidate
    apply (mem_trueCoordinates assignment candidate).2
    have hTrue := (mem_trueCoordinates
      (flipAssignment coordinate assignment) candidate).1
        (hSubset hCandidate)
    by_cases hSame : candidate = coordinate
    · subst candidate
      exact False.elim (hUnused hCandidate)
    · simpa [flipAssignment_apply_of_ne hSame] using hTrue
  · intro hSubset candidate hCandidate
    apply (mem_trueCoordinates
      (flipAssignment coordinate assignment) candidate).2
    have hTrue :=
      (mem_trueCoordinates assignment candidate).1 (hSubset hCandidate)
    by_cases hSame : candidate = coordinate
    · subst candidate
      exact False.elim (hUnused hCandidate)
    · simpa [flipAssignment_apply_of_ne hSame] using hTrue

/-- The visible coordinate occupied by one of the four suffix bits. -/
def blockParitySuffixCoordinate {q : Nat} (coordinate : Fin 4) :
    BlockParityVar q :=
  Sum.inr (Sum.inl coordinate)

theorem blockParityState_flipSuffix
    {q : Nat} (label : BitVec q) (suffix : BitVec 4)
    (coordinate : Fin 4) :
    blockParityState label (flipBit coordinate suffix) =
      flipAssignment (blockParitySuffixCoordinate coordinate)
        (blockParityState label suffix) := by
  funext candidate
  rcases candidate with prefixCandidate | suffixOrMarker
  · simp [blockParityState, flipAssignment, blockParitySuffixCoordinate]
  · rcases suffixOrMarker with suffixCandidate | marker
    · by_cases hSame : suffixCandidate = coordinate
      · subst suffixCandidate
        simp [blockParityState, flipAssignment, blockParitySuffixCoordinate]
      · simp [blockParityState, flipAssignment, blockParitySuffixCoordinate,
          hSame, flipBit_apply_of_ne hSame]
    · simp [blockParityState, flipAssignment, blockParitySuffixCoordinate]

/-- A cubic scope cannot contain all four suffix coordinates. -/
theorem exists_blockParitySuffixCoordinate_not_mem
    {q : Nat} (scope : FeatureScope (BlockParityVar q) 3) :
    ∃ coordinate : Fin 4,
      blockParitySuffixCoordinate coordinate ∉ scope.1 := by
  classical
  by_contra hNone
  push_neg at hNone
  let embedding : Fin 4 ↪ BlockParityVar q :=
    ⟨blockParitySuffixCoordinate, by
      intro left right hEqual
      simp only [blockParitySuffixCoordinate, Sum.inr.injEq,
        Sum.inl.injEq] at hEqual
      exact hEqual⟩
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

/-- Degree-at-most-three moment of the candidate selected by a Boolean truth
table on the prefix cube.  Writing it as an iterated sum avoids quotienting
the manifestly injective state embedding. -/
def blockParityMoment {q : Nat}
    (test : BitVec q -> Bool)
    (scope : FeatureScope (BlockParityVar q) 3) : ℚ :=
  ∑ label : BitVec q, ∑ suffix : BitVec 4,
    if parityFour suffix = test label then
      rationalMonomialValue scope.1 (blockParityState label suffix)
    else 0

/-- All block-parity candidates have exactly the same visible cubic moment
profile, uniformly in the prefix width and in the two truth tables. -/
theorem blockParityMoment_eq
    {q : Nat} (left right : BitVec q -> Bool) :
    ∀ scope : FeatureScope (BlockParityVar q) 3,
      blockParityMoment left scope = blockParityMoment right scope := by
  intro scope
  classical
  rcases exists_blockParitySuffixCoordinate_not_mem scope with
    ⟨coordinate, hUnused⟩
  unfold blockParityMoment
  apply Finset.sum_congr rfl
  intro label _
  by_cases hEqual : left label = right label
  · rw [hEqual]
  · have hOpposite : right label = !left label := by
      cases hLeft : left label <;> cases hRight : right label <;>
        simp_all
    let summand : BitVec 4 → ℚ := fun suffix =>
      if parityFour suffix = left label then
        rationalMonomialValue scope.1 (blockParityState label suffix)
      else 0
    have hReindex := (flipBitEquiv coordinate).sum_comp summand
    calc
      (∑ suffix : BitVec 4,
          if parityFour suffix = left label then
            rationalMonomialValue scope.1 (blockParityState label suffix)
          else 0) = ∑ suffix : BitVec 4,
          summand (flipBit coordinate suffix) := hReindex.symm
      _ = ∑ suffix : BitVec 4,
          if parityFour suffix = right label then
            rationalMonomialValue scope.1 (blockParityState label suffix)
          else 0 := by
        apply Finset.sum_congr rfl
        intro suffix _
        change
          (if parityFour (flipBit coordinate suffix) = left label then
            rationalMonomialValue scope.1
              (blockParityState label (flipBit coordinate suffix))
          else 0) = _
        rw [blockParityState_flipSuffix,
          rationalMonomialValue_flipAssignment_of_not_mem
            scope.1 (blockParityState label suffix)
              (blockParitySuffixCoordinate coordinate) hUnused]
        rw [parityFour_flipBit]
        rw [hOpposite]
        cases hParity : parityFour suffix <;>
          cases hLeft : left label <;>
            simp

end KLocality
