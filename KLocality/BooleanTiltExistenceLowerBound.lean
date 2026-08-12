import KLocality.BinarySubsetTransform
import KLocality.BooleanTiltTrade
import KLocality.LatentPadding
import KLocality.UniformExplicitCubicLowerBound

namespace KLocality

open scoped BigOperators

set_option maxRecDepth 30000

/-!
# Exponential Boolean-tilt lower bounds by interpolation

The powers-of-powers construction produces, at a requested hidden budget, two
distinct finite families of binary candidate monomials with the same expanded
cubic profile histogram.  The binary subset transform proves that some
two-level evaluation `x |-> 2 ^ f(x)` separates those families.  Consequently
there exists a Boolean function `f` whose full-support tilt `D_f` has the same
exponential cubic-localization lower bound.

This is an existence theorem: `f` is selected from the noncomputably chosen
profile collision.  It is therefore not an explicit circuit lower bound.  Its
purpose is to isolate the precise remaining challenge: construct a
low-description-complexity separating test for the collision.
-/

/-- A binary test on candidate blocks, extended to a Boolean function on the
whole visible cube.  The reserved filler state and every state outside the
block range are false. -/
def uniformCubicBooleanTest
    (n : Nat) (test : UniformCubicCandidate n) (visible : BitVec n) : Bool :=
  if hValue : binaryAssignmentValue visible < uniformCubicBlockCount n then
    decide (test ⟨binaryAssignmentValue visible, hValue⟩ = 1)
  else false

@[simp]
theorem uniformCubicBooleanTest_block
    (n : Nat) (test : UniformCubicCandidate n)
    (block : Fin (uniformCubicBlockCount n)) :
    uniformCubicBooleanTest n test (uniformCubicBlockState n block) =
      decide (test block = 1) := by
  have hBlockLt : block.val < 2 ^ n :=
    lt_trans block.isLt (uniformCubicBlockCount_lt_two_pow n)
  simp [uniformCubicBooleanTest, uniformCubicBlockState,
    binaryAssignmentValue_binaryAssignment_of_lt hBlockLt, block.isLt]

@[simp]
theorem uniformCubicBooleanTest_filler
    (n : Nat) (test : UniformCubicCandidate n) :
    uniformCubicBooleanTest n test (uniformCubicFillerState n) = false := by
  simp [uniformCubicBooleanTest, uniformCubicFillerState,
    binaryAssignmentValue_binaryAssignment_of_lt
      (uniformCubicBlockCount_lt_two_pow n)]

/-- On one candidate tuple, the Boolean test counts exactly the intersection
of the candidate and test digit sets. -/
theorem booleanTiltTrueCount_uniformCubicCandidateTuple
    (n : Nat) (test candidate : UniformCubicCandidate n) :
    booleanTiltTrueCount (uniformCubicBooleanTest n test)
        (uniformCubicCandidateTuple n candidate) =
      binarySubsetOverlapCount test candidate := by
  classical
  unfold booleanTiltTrueCount binarySubsetOverlapCount
  rw [← (uniformCubicIndexEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro block _
  generalize hCandidate : candidate block = candidateValue
  generalize hTest : test block = testValue
  fin_cases candidateValue <;>
    fin_cases testValue <;>
      rw [Fin.sum_univ_two] <;>
      norm_num [uniformCubicCandidateTuple_index,
        uniformCubicBooleanTest_block, uniformCubicBooleanTest_filler,
        hCandidate, hTest]

/-- The positive Boolean-tilt code of the collision certificate is its binary
subset response profile. -/
theorem uniformCubicCertificate_booleanTiltPositiveCode
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n)
    (test : UniformCubicCandidate n) :
    (uniformCubicCertificate n latentBits hParameter).booleanTiltPositiveCode
        (uniformCubicBooleanTest n test) =
      binarySubsetFamilyProfile
        (uniformCubicChosenCollision n latentBits hParameter).left test := by
  classical
  unfold MarginalTradeCertificate.booleanTiltPositiveCode
  change
    (∑ term : Fin (uniformCubicTermCount n latentBits hParameter),
      2 ^ booleanTiltTrueCount (uniformCubicBooleanTest n test)
        (uniformCubicCandidateTuple n
          (uniformCubicPositiveEnumeration n latentBits hParameter term).1)) = _
  simp_rw [booleanTiltTrueCount_uniformCubicCandidateTuple]
  calc
    (∑ term : Fin (uniformCubicTermCount n latentBits hParameter),
        2 ^ binarySubsetOverlapCount test
          (uniformCubicPositiveEnumeration n latentBits hParameter term).1) =
        ∑ candidate :
            (uniformCubicChosenCollision n latentBits hParameter).left,
          2 ^ binarySubsetOverlapCount test candidate.1 := by
      exact (uniformCubicPositiveEnumeration n latentBits hParameter).sum_comp
        (fun candidate => 2 ^ binarySubsetOverlapCount test candidate.1)
    _ = ∑ candidate ∈
          (uniformCubicChosenCollision n latentBits hParameter).left,
        2 ^ binarySubsetOverlapCount test candidate := by
      exact Finset.sum_coe_sort
        (uniformCubicChosenCollision n latentBits hParameter).left
        (fun candidate => (2 ^ binarySubsetOverlapCount test candidate : Nat))
    _ = _ := by
      unfold binarySubsetFamilyProfile
      simp_rw [binarySubsetKernelNat_eq_two_pow_overlapCount]

/-- The negative Boolean-tilt code is the response profile of the other side
of the collision. -/
theorem uniformCubicCertificate_booleanTiltNegativeCode
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n)
    (test : UniformCubicCandidate n) :
    (uniformCubicCertificate n latentBits hParameter).booleanTiltNegativeCode
        (uniformCubicBooleanTest n test) =
      binarySubsetFamilyProfile
        (uniformCubicChosenCollision n latentBits hParameter).right test := by
  classical
  unfold MarginalTradeCertificate.booleanTiltNegativeCode
  change
    (∑ term : Fin (uniformCubicTermCount n latentBits hParameter),
      2 ^ booleanTiltTrueCount (uniformCubicBooleanTest n test)
        (uniformCubicCandidateTuple n
          (uniformCubicNegativeEnumeration n latentBits hParameter term).1)) = _
  simp_rw [booleanTiltTrueCount_uniformCubicCandidateTuple]
  calc
    (∑ term : Fin (uniformCubicTermCount n latentBits hParameter),
        2 ^ binarySubsetOverlapCount test
          (uniformCubicNegativeEnumeration n latentBits hParameter term).1) =
        ∑ candidate :
            (uniformCubicChosenCollision n latentBits hParameter).right,
          2 ^ binarySubsetOverlapCount test candidate.1 := by
      exact (uniformCubicNegativeEnumeration n latentBits hParameter).sum_comp
        (fun candidate => 2 ^ binarySubsetOverlapCount test candidate.1)
    _ = ∑ candidate ∈
          (uniformCubicChosenCollision n latentBits hParameter).right,
        2 ^ binarySubsetOverlapCount test candidate := by
      exact Finset.sum_coe_sort
        (uniformCubicChosenCollision n latentBits hParameter).right
        (fun candidate => (2 ^ binarySubsetOverlapCount test candidate : Nat))
    _ = _ := by
      unfold binarySubsetFamilyProfile
      simp_rw [binarySubsetKernelNat_eq_two_pow_overlapCount]

/-- Every nontrivial profile collision is detected by some full-support
Boolean tilt. -/
theorem exists_booleanTilt_obstructing_uniformCubicCollision
    (n latentBits : Nat)
    (hParameter :
      uniformCubicCoordinateLogLog n latentBits +
          uniformCubicProfileLog n latentBits <
        uniformCubicBlockCount n) :
    ∃ f : BitVec n -> Bool,
      ¬HasKLocalizationBits 3 latentBits n (booleanTiltDistribution f) := by
  let collision := uniformCubicChosenCollision n latentBits hParameter
  rcases exists_binarySubsetTest_of_ne collision.distinct with
    ⟨test, hTest⟩
  let f := uniformCubicBooleanTest n test
  refine ⟨f, ?_⟩
  apply (uniformCubicCertificate n latentBits hParameter).obstructs_booleanTilt_of_code_ne
  change
    (uniformCubicCertificate n latentBits hParameter).booleanTiltPositiveCode
        (uniformCubicBooleanTest n test) ≠
      (uniformCubicCertificate n latentBits hParameter).booleanTiltNegativeCode
        (uniformCubicBooleanTest n test)
  rw [uniformCubicCertificate_booleanTiltPositiveCode,
    uniformCubicCertificate_booleanTiltNegativeCode]
  exact hTest

/-- On `4m+24` visible bits there exists a two-level, full-support rational
tilt whose cubic localization complexity exceeds `2^m`. -/
theorem exists_superlinearBooleanTilt_localizationComplexity_gt
    (scale : Nat) :
    ∃ f : BitVec (superlinearCubicVisibleBits scale) -> Bool,
      2 ^ scale < localizationComplexityBits 3
        (superlinearCubicVisibleBits scale) (booleanTiltDistribution f) := by
  have hParameter := superlinearCubic_parameter_inequality
    (scale := scale) (latentBits := 2 ^ scale) (le_refl _)
  rcases exists_booleanTilt_obstructing_uniformCubicCollision
      (superlinearCubicVisibleBits scale) (2 ^ scale) hParameter with
    ⟨f, hNoLocalization⟩
  exact ⟨f, localizationComplexityBits_gt_of_not_hasKLocalization
    (by norm_num) (booleanTiltDistribution f) hNoLocalization⟩

/-- Direct gate-count form: for the selected `f`, every supplied sequential
NAND circuit computing it has more than `2^m` gates. -/
theorem exists_superlinearBooleanTilt_nandGateLowerBound
    (scale : Nat) :
    ∃ f : BitVec (superlinearCubicVisibleBits scale) -> Bool,
      2 ^ scale < localizationComplexityBits 3
          (superlinearCubicVisibleBits scale) (booleanTiltDistribution f) ∧
        ∀ (gateCount : Nat)
          (recognizer : NANDCircuit.Recognizer
            (superlinearCubicVisibleBits scale) gateCount),
          recognizer.eval = f -> 2 ^ scale < gateCount := by
  rcases exists_superlinearBooleanTilt_localizationComplexity_gt scale with
    ⟨f, hLocalization⟩
  refine ⟨f, hLocalization, ?_⟩
  intro gateCount recognizer hComputes
  exact lt_of_lt_of_le hLocalization
    (recognizer.localizationComplexityBits_three_booleanTilt_le hComputes)

/-- For the Boolean function selected above, every constant-free NAND
recognizer (when supplied) has more than `2^m` gates.  The separate existence
of a recognizer for every truth table is not yet part of the sequential NAND
API, so it remains an explicit hypothesis here. -/
theorem exists_superlinearBooleanTilt_CNAND_lowerBound
    (scale : Nat) :
    ∃ f : BitVec (superlinearCubicVisibleBits scale) -> Bool,
      2 ^ scale < localizationComplexityBits 3
          (superlinearCubicVisibleBits scale) (booleanTiltDistribution f) ∧
        ∀ hCircuitExists : ∃ gateCount,
          NANDCircuit.NANDRecognizerWitness
            (superlinearCubicVisibleBits scale)
            (NANDCircuit.booleanTrueInputs f) gateCount,
          2 ^ scale < NANDCircuit.CNAND
            (superlinearCubicVisibleBits scale)
            (NANDCircuit.booleanTrueInputs f) hCircuitExists := by
  rcases exists_superlinearBooleanTilt_localizationComplexity_gt scale with
    ⟨f, hLocalization⟩
  refine ⟨f, hLocalization, ?_⟩
  intro hCircuitExists
  exact lt_of_lt_of_le hLocalization
    (NANDCircuit.localizationComplexityBits_three_booleanTilt_le_CNAND
      f hCircuitExists)

end KLocality
