import KLocality.Core

namespace KLocality

open scoped BigOperators

/-!
# An invertible binary subset transform

For binary vectors `test` and `candidate`, put

`K(test,candidate) = 2 ^ |test intersect candidate|`.

The one-coordinate matrix is `[[1,1],[1,2]]`, whose integer inverse is
`[[2,-1],[-1,1]]`.  Tensoring over the coordinates shows that a finite set of
binary candidates is determined by all of the sums

`sum_candidate K(test,candidate)`.

This elementary interpolation fact is the bridge from a nontrivial profile
collision to a two-level Boolean tilt that detects it.
-/

/-- One coordinate of the binary subset kernel. -/
def binarySubsetKernelEntry (test candidate : Fin 2) : ℤ :=
  if test.val = 1 ∧ candidate.val = 1 then 2 else 1

/-- One coordinate of the inverse binary subset kernel. -/
def binarySubsetInverseEntry (candidate test : Fin 2) : ℤ :=
  if candidate.val = 0 then
    if test.val = 0 then 2 else -1
  else if test.val = 0 then -1 else 1

theorem binarySubsetEntry_orthogonal (candidate other : Fin 2) :
    (∑ test : Fin 2,
      binarySubsetInverseEntry candidate test *
        binarySubsetKernelEntry test other) =
      if candidate = other then 1 else 0 := by
  fin_cases candidate <;> fin_cases other <;>
    norm_num [binarySubsetInverseEntry, binarySubsetKernelEntry,
      Fin.sum_univ_two]

/-- Tensor-product subset kernel on binary vectors. -/
def binarySubsetKernelInt
    {width : Nat} (test candidate : Fin width -> Fin 2) : ℤ :=
  ∏ coordinate : Fin width,
    binarySubsetKernelEntry (test coordinate) (candidate coordinate)

/-- Tensor product of the one-coordinate inverse kernel. -/
def binarySubsetInverseKernel
    {width : Nat} (candidate test : Fin width -> Fin 2) : ℤ :=
  ∏ coordinate : Fin width,
    binarySubsetInverseEntry (candidate coordinate) (test coordinate)

theorem binarySubsetKernel_orthogonal
    {width : Nat} (candidate other : Fin width -> Fin 2) :
    (∑ test : Fin width -> Fin 2,
      binarySubsetInverseKernel candidate test *
        binarySubsetKernelInt test other) =
      if candidate = other then 1 else 0 := by
  classical
  calc
    (∑ test : Fin width -> Fin 2,
        binarySubsetInverseKernel candidate test *
          binarySubsetKernelInt test other) =
        ∑ test : Fin width -> Fin 2,
          ∏ coordinate : Fin width,
            (binarySubsetInverseEntry (candidate coordinate) (test coordinate) *
              binarySubsetKernelEntry (test coordinate) (other coordinate)) := by
      apply Finset.sum_congr rfl
      intro test _
      exact Finset.prod_mul_distrib.symm
    _ = ∏ coordinate : Fin width,
        ∑ bit : Fin 2,
          (binarySubsetInverseEntry (candidate coordinate) bit *
            binarySubsetKernelEntry bit (other coordinate)) := by
      exact (Fintype.prod_sum
        (fun coordinate : Fin width => fun bit : Fin 2 =>
          binarySubsetInverseEntry (candidate coordinate) bit *
            binarySubsetKernelEntry bit (other coordinate))).symm
    _ = ∏ coordinate : Fin width,
        if candidate coordinate = other coordinate then 1 else 0 := by
      apply Finset.prod_congr rfl
      intro coordinate _
      exact binarySubsetEntry_orthogonal _ _
    _ = if candidate = other then 1 else 0 := by
      by_cases hEqual : candidate = other
      · subst other
        simp
      · rw [if_neg hEqual]
        have hCoordinate : ∃ coordinate, candidate coordinate ≠ other coordinate := by
          by_contra hNone
          push_neg at hNone
          exact hEqual (funext hNone)
        rcases hCoordinate with ⟨coordinate, hCoordinate⟩
        exact Finset.prod_eq_zero (Finset.mem_univ coordinate)
          (by simp [hCoordinate])

/-- Linear subset transform over the integers. -/
def binarySubsetTransformInt
    {width : Nat} (coefficients : (Fin width -> Fin 2) -> ℤ)
    (test : Fin width -> Fin 2) : ℤ :=
  ∑ candidate : Fin width -> Fin 2,
    binarySubsetKernelInt test candidate * coefficients candidate

/-- Explicit inversion of the binary subset transform. -/
theorem binarySubsetTransformInt_recover
    {width : Nat} (coefficients : (Fin width -> Fin 2) -> ℤ)
    (candidate : Fin width -> Fin 2) :
    (∑ test : Fin width -> Fin 2,
      binarySubsetInverseKernel candidate test *
        binarySubsetTransformInt coefficients test) =
      coefficients candidate := by
  classical
  unfold binarySubsetTransformInt
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ candidate' : Fin width -> Fin 2,
        ∑ test : Fin width -> Fin 2,
          binarySubsetInverseKernel candidate test *
            (binarySubsetKernelInt test candidate' * coefficients candidate')) =
        ∑ candidate' : Fin width -> Fin 2,
          (∑ test : Fin width -> Fin 2,
            binarySubsetInverseKernel candidate test *
              binarySubsetKernelInt test candidate') *
                coefficients candidate' := by
      apply Finset.sum_congr rfl
      intro candidate' _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro test _
      ring
    _ = coefficients candidate := by
      simp_rw [binarySubsetKernel_orthogonal]
      rw [Fintype.sum_eq_single candidate]
      · simp
      · intro other hOther
        simp [Ne.symm hOther]

theorem binarySubsetTransformInt_injective {width : Nat} :
    Function.Injective
      (binarySubsetTransformInt (width := width)) := by
  intro left right hTransforms
  funext candidate
  rw [← binarySubsetTransformInt_recover left candidate,
    ← binarySubsetTransformInt_recover right candidate, hTransforms]

/-- Natural-number version of the subset kernel. -/
def binarySubsetKernelNat
    {width : Nat} (test candidate : Fin width -> Fin 2) : Nat :=
  ∏ coordinate : Fin width,
    if test coordinate = 1 ∧ candidate coordinate = 1 then 2 else 1

/-- Number of coordinates selected by both binary vectors. -/
def binarySubsetOverlapCount
    {width : Nat} (test candidate : Fin width -> Fin 2) : Nat :=
  ∑ coordinate : Fin width,
    if test coordinate = 1 ∧ candidate coordinate = 1 then 1 else 0

theorem binarySubsetKernelNat_eq_two_pow_overlapCount
    {width : Nat} (test candidate : Fin width -> Fin 2) :
    binarySubsetKernelNat test candidate =
      2 ^ binarySubsetOverlapCount test candidate := by
  classical
  unfold binarySubsetKernelNat binarySubsetOverlapCount
  calc
    (∏ coordinate : Fin width,
        if test coordinate = 1 ∧ candidate coordinate = 1 then 2 else 1) =
        ∏ coordinate : Fin width,
          2 ^ (if test coordinate = 1 ∧ candidate coordinate = 1
            then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro coordinate _
      split <;> norm_num
    _ = 2 ^ ∑ coordinate : Fin width,
        (if test coordinate = 1 ∧ candidate coordinate = 1
          then 1 else 0) := by
      simpa using (Finset.prod_pow_eq_pow_sum
        (Finset.univ : Finset (Fin width))
          (fun coordinate : Fin width =>
            if test coordinate = 1 ∧ candidate coordinate = 1
            then 1 else 0) (2 : Nat))

theorem binarySubsetKernelInt_eq_natCast
    {width : Nat} (test candidate : Fin width -> Fin 2) :
    binarySubsetKernelInt test candidate =
      (binarySubsetKernelNat test candidate : ℤ) := by
  classical
  unfold binarySubsetKernelInt binarySubsetKernelNat
  push_cast
  apply Finset.prod_congr rfl
  intro coordinate _
  simp only [binarySubsetKernelEntry]
  by_cases hEntry : test coordinate = 1 ∧ candidate coordinate = 1
  · simp [hEntry]
  · have hVals : ¬((test coordinate).val = 1 ∧
        (candidate coordinate).val = 1) := by
      simpa [Fin.ext_iff] using hEntry
    simp [hEntry, hVals]

/-- The response profile of a finite candidate family to all binary tests. -/
def binarySubsetFamilyProfile
    {width : Nat} (family : Finset (Fin width -> Fin 2))
    (test : Fin width -> Fin 2) : Nat :=
  ∑ candidate ∈ family, binarySubsetKernelNat test candidate

/-- Integer indicator of membership in a finite candidate family. -/
def binarySubsetFamilyIndicator
    {width : Nat} (family : Finset (Fin width -> Fin 2))
    (candidate : Fin width -> Fin 2) : ℤ :=
  if candidate ∈ family then 1 else 0

theorem binarySubsetTransformInt_indicator
    {width : Nat} (family : Finset (Fin width -> Fin 2))
    (test : Fin width -> Fin 2) :
    binarySubsetTransformInt (binarySubsetFamilyIndicator family) test =
      (binarySubsetFamilyProfile family test : ℤ) := by
  classical
  unfold binarySubsetTransformInt binarySubsetFamilyIndicator
  unfold binarySubsetFamilyProfile
  push_cast
  simp [binarySubsetKernelInt_eq_natCast]

/-- Distinct finite candidate families are separated by at least one binary
test. -/
theorem binarySubsetFamilyProfile_injective {width : Nat} :
    Function.Injective (binarySubsetFamilyProfile (width := width)) := by
  classical
  intro left right hProfiles
  have hIndicators : binarySubsetFamilyIndicator left =
      binarySubsetFamilyIndicator right := by
    apply binarySubsetTransformInt_injective
    funext test
    rw [binarySubsetTransformInt_indicator,
      binarySubsetTransformInt_indicator, hProfiles]
  ext candidate
  have hAtCandidate := congrFun hIndicators candidate
  by_cases hLeft : candidate ∈ left <;>
    by_cases hRight : candidate ∈ right <;>
      simp_all [binarySubsetFamilyIndicator]

/-- Pointwise separation form of injectivity. -/
theorem exists_binarySubsetTest_of_ne
    {width : Nat} {left right : Finset (Fin width -> Fin 2)}
    (hDistinct : left ≠ right) :
    ∃ test : Fin width -> Fin 2,
      binarySubsetFamilyProfile left test ≠
        binarySubsetFamilyProfile right test := by
  by_contra hNone
  push_neg at hNone
  exact hDistinct (binarySubsetFamilyProfile_injective (funext hNone))

end KLocality
