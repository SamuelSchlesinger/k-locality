import KLocality.Core

namespace KLocality

open scoped BigOperators

/-!
# Binary agreement transforms

For binary vectors `test` and `candidate`, this module studies the tensor
kernel

`A_base(test,candidate) = product_i (if test_i = candidate_i then base else 1)`.

The block-parity cubic fiber specializes to `base = 256`: every agreeing
four-face contributes eight common visible states, hence a factor `2^8`.
The kernel is diagonal in the Walsh basis, with one-coordinate eigenvalues
`base + 1` and `base - 1`.  An explicit adjugate tensor also proves
injectivity over the integers whenever `base^2 - 1` is nonzero.
-/

/-- One coordinate of the agreement kernel. -/
def binaryAgreementEntry (base : ℤ) (test candidate : Fin 2) : ℤ :=
  if test = candidate then base else 1

/-- One coordinate of the adjugate agreement kernel. -/
def binaryAgreementAdjugateEntry
    (base : ℤ) (candidate test : Fin 2) : ℤ :=
  if candidate = test then base else -1

theorem binaryAgreementEntry_adjugate
    (base : ℤ) (candidate other : Fin 2) :
    (∑ test : Fin 2,
      binaryAgreementAdjugateEntry base candidate test *
        binaryAgreementEntry base test other) =
      if candidate = other then base ^ 2 - 1 else 0 := by
  fin_cases candidate <;> fin_cases other <;>
    norm_num [binaryAgreementAdjugateEntry, binaryAgreementEntry,
      Fin.sum_univ_two] <;> ring

/-- Tensor product of the one-coordinate agreement kernel. -/
def binaryAgreementKernel
    {width : Nat} (base : ℤ)
    (test candidate : Fin width -> Fin 2) : ℤ :=
  ∏ coordinate : Fin width,
    binaryAgreementEntry base (test coordinate) (candidate coordinate)

/-- Number of coordinates on which two binary vectors agree. -/
def binaryAgreementCount
    {width : Nat} (test candidate : Fin width -> Fin 2) : Nat :=
  ((Finset.univ : Finset (Fin width)).filter fun coordinate =>
    test coordinate = candidate coordinate).card

theorem binaryAgreementKernel_eq_pow_agreementCount
    {width : Nat} (base : ℤ)
    (test candidate : Fin width -> Fin 2) :
    binaryAgreementKernel base test candidate =
      base ^ binaryAgreementCount test candidate := by
  classical
  unfold binaryAgreementKernel binaryAgreementEntry binaryAgreementCount
  rw [Finset.prod_ite]
  simp

/-- Tensor product of the one-coordinate adjugate. -/
def binaryAgreementAdjugateKernel
    {width : Nat} (base : ℤ)
    (candidate test : Fin width -> Fin 2) : ℤ :=
  ∏ coordinate : Fin width,
    binaryAgreementAdjugateEntry base
      (candidate coordinate) (test coordinate)

theorem binaryAgreementKernel_adjugate
    {width : Nat} (base : ℤ)
    (candidate other : Fin width -> Fin 2) :
    (∑ test : Fin width -> Fin 2,
      binaryAgreementAdjugateKernel base candidate test *
        binaryAgreementKernel base test other) =
      if candidate = other then (base ^ 2 - 1) ^ width else 0 := by
  classical
  calc
    (∑ test : Fin width -> Fin 2,
        binaryAgreementAdjugateKernel base candidate test *
          binaryAgreementKernel base test other) =
        ∑ test : Fin width -> Fin 2,
          ∏ coordinate : Fin width,
            (binaryAgreementAdjugateEntry base
                (candidate coordinate) (test coordinate) *
              binaryAgreementEntry base
                (test coordinate) (other coordinate)) := by
      apply Finset.sum_congr rfl
      intro test _
      exact Finset.prod_mul_distrib.symm
    _ = ∏ coordinate : Fin width,
        ∑ bit : Fin 2,
          (binaryAgreementAdjugateEntry base
              (candidate coordinate) bit *
            binaryAgreementEntry base bit (other coordinate)) := by
      exact (Fintype.prod_sum
        (fun coordinate : Fin width => fun bit : Fin 2 =>
          binaryAgreementAdjugateEntry base
              (candidate coordinate) bit *
            binaryAgreementEntry base bit (other coordinate))).symm
    _ = ∏ coordinate : Fin width,
        if candidate coordinate = other coordinate then
          base ^ 2 - 1 else 0 := by
      apply Finset.prod_congr rfl
      intro coordinate _
      exact binaryAgreementEntry_adjugate base _ _
    _ = if candidate = other then (base ^ 2 - 1) ^ width else 0 := by
      by_cases hEqual : candidate = other
      · subst other
        simp
      · rw [if_neg hEqual]
        have hCoordinate :
            ∃ coordinate, candidate coordinate ≠ other coordinate := by
          by_contra hNone
          push_neg at hNone
          exact hEqual (funext hNone)
        rcases hCoordinate with ⟨coordinate, hCoordinate⟩
        exact Finset.prod_eq_zero (Finset.mem_univ coordinate)
          (by simp [hCoordinate])

/-- Linear transform defined by the binary agreement kernel. -/
def binaryAgreementTransform
    {width : Nat} (base : ℤ)
    (coefficients : (Fin width -> Fin 2) -> ℤ)
    (test : Fin width -> Fin 2) : ℤ :=
  ∑ candidate : Fin width -> Fin 2,
    binaryAgreementKernel base test candidate * coefficients candidate

/-- Applying the tensor adjugate recovers a fixed nonzero scalar multiple of
every coefficient. -/
theorem binaryAgreementTransform_recover
    {width : Nat} (base : ℤ)
    (coefficients : (Fin width -> Fin 2) -> ℤ)
    (candidate : Fin width -> Fin 2) :
    (∑ test : Fin width -> Fin 2,
      binaryAgreementAdjugateKernel base candidate test *
        binaryAgreementTransform base coefficients test) =
      (base ^ 2 - 1) ^ width * coefficients candidate := by
  classical
  unfold binaryAgreementTransform
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ candidate' : Fin width -> Fin 2,
        ∑ test : Fin width -> Fin 2,
          binaryAgreementAdjugateKernel base candidate test *
            (binaryAgreementKernel base test candidate' *
              coefficients candidate')) =
        ∑ candidate' : Fin width -> Fin 2,
          (∑ test : Fin width -> Fin 2,
            binaryAgreementAdjugateKernel base candidate test *
              binaryAgreementKernel base test candidate') *
                coefficients candidate' := by
      apply Finset.sum_congr rfl
      intro candidate' _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro test _
      ring
    _ = (base ^ 2 - 1) ^ width * coefficients candidate := by
      simp_rw [binaryAgreementKernel_adjugate]
      rw [Fintype.sum_eq_single candidate]
      · simp
      · intro other hOther
        simp [Ne.symm hOther]

theorem binaryAgreementTransform_injective
    {width : Nat} {base : ℤ} (hBase : base ^ 2 - 1 ≠ 0) :
    Function.Injective
      (binaryAgreementTransform (width := width) base) := by
  intro left right hTransforms
  funext candidate
  apply mul_left_cancel₀ (pow_ne_zero width hBase)
  rw [← binaryAgreementTransform_recover,
    ← binaryAgreementTransform_recover, hTransforms]

/-! ## Walsh diagonalization -/

/-- One-coordinate Walsh character. -/
def binaryWalshEntry (selected bit : Fin 2) : ℤ :=
  if selected = 1 ∧ bit = 1 then -1 else 1

/-- Tensor Walsh character indexed by a binary vector. -/
def binaryWalshCharacter
    {width : Nat} (selected point : Fin width -> Fin 2) : ℤ :=
  ∏ coordinate : Fin width,
    binaryWalshEntry (selected coordinate) (point coordinate)

/-- Product form of the Walsh eigenvalue. -/
def binaryAgreementEigenvalue
    {width : Nat} (base : ℤ) (selected : Fin width -> Fin 2) : ℤ :=
  ∏ coordinate : Fin width,
    if selected coordinate = 1 then base - 1 else base + 1

theorem binaryAgreementEntry_walsh
    (base : ℤ) (selected test : Fin 2) :
    (∑ candidate : Fin 2,
      binaryAgreementEntry base test candidate *
        binaryWalshEntry selected candidate) =
      (if selected = 1 then base - 1 else base + 1) *
        binaryWalshEntry selected test := by
  fin_cases selected <;> fin_cases test <;>
    norm_num [binaryAgreementEntry, binaryWalshEntry, Fin.sum_univ_two] <;>
    ring

/-- Every Walsh character is an eigenvector of the agreement transform. -/
theorem binaryAgreementKernel_walsh_eigenvector
    {width : Nat} (base : ℤ)
    (selected test : Fin width -> Fin 2) :
    (∑ candidate : Fin width -> Fin 2,
      binaryAgreementKernel base test candidate *
        binaryWalshCharacter selected candidate) =
      binaryAgreementEigenvalue base selected *
        binaryWalshCharacter selected test := by
  classical
  calc
    (∑ candidate : Fin width -> Fin 2,
        binaryAgreementKernel base test candidate *
          binaryWalshCharacter selected candidate) =
        ∑ candidate : Fin width -> Fin 2,
          ∏ coordinate : Fin width,
            (binaryAgreementEntry base
                (test coordinate) (candidate coordinate) *
              binaryWalshEntry
                (selected coordinate) (candidate coordinate)) := by
      apply Finset.sum_congr rfl
      intro candidate _
      exact Finset.prod_mul_distrib.symm
    _ = ∏ coordinate : Fin width,
        ∑ bit : Fin 2,
          (binaryAgreementEntry base (test coordinate) bit *
            binaryWalshEntry (selected coordinate) bit) := by
      exact (Fintype.prod_sum
        (fun coordinate : Fin width => fun bit : Fin 2 =>
          binaryAgreementEntry base (test coordinate) bit *
            binaryWalshEntry (selected coordinate) bit)).symm
    _ = ∏ coordinate : Fin width,
        ((if selected coordinate = 1 then base - 1 else base + 1) *
          binaryWalshEntry (selected coordinate) (test coordinate)) := by
      apply Finset.prod_congr rfl
      intro coordinate _
      exact binaryAgreementEntry_walsh base _ _
    _ = binaryAgreementEigenvalue base selected *
        binaryWalshCharacter selected test := by
      exact Finset.prod_mul_distrib

/-- The `256`-agreement transform arising from four-bit parity blocks is
integer-injective. -/
theorem binaryAgreementTransform_256_injective {width : Nat} :
    Function.Injective
      (binaryAgreementTransform (width := width) 256) := by
  apply binaryAgreementTransform_injective
  norm_num

/-! ## Walsh transform of binary product columns -/

/-- A column obtained by choosing one of two ring elements independently at
every coordinate.  The one-hidden block-parity columns have exactly this
form, with the two entries given by the even- and odd-parity products in one
four-face. -/
def binaryProductColumn
    {R : Type*} [CommRing R] {width : Nat}
    (entry : Fin width -> Fin 2 -> R)
    (choice : Fin width -> Fin 2) : R :=
  ∏ coordinate : Fin width, entry coordinate (choice coordinate)

/-- The one-coordinate Walsh character, interpreted in an arbitrary
commutative ring. -/
def binaryWalshEntryIn
    {R : Type*} [CommRing R] (selected bit : Fin 2) : R :=
  if selected = 1 ∧ bit = 1 then -1 else 1

/-- The tensor Walsh character, interpreted in an arbitrary commutative
ring. -/
def binaryWalshCharacterIn
    {R : Type*} [CommRing R] {width : Nat}
    (selected point : Fin width -> Fin 2) : R :=
  ∏ coordinate : Fin width,
    binaryWalshEntryIn (selected coordinate) (point coordinate)

/-- Exact Walsh factorization of a binary product-column family.  Selected
coordinates contribute a difference, while unselected coordinates contribute
a sum. -/
theorem binaryProductColumn_walshTransform
    {R : Type*} [CommRing R] {width : Nat}
    (entry : Fin width -> Fin 2 -> R)
    (selected : Fin width -> Fin 2) :
    (∑ choice : Fin width -> Fin 2,
      binaryWalshCharacterIn selected choice *
        binaryProductColumn entry choice) =
      ∏ coordinate : Fin width,
        if selected coordinate = 1 then
          entry coordinate 0 - entry coordinate 1
        else entry coordinate 0 + entry coordinate 1 := by
  classical
  calc
    (∑ choice : Fin width -> Fin 2,
        binaryWalshCharacterIn selected choice *
          binaryProductColumn entry choice) =
        ∑ choice : Fin width -> Fin 2,
          ∏ coordinate : Fin width,
            (binaryWalshEntryIn
                (selected coordinate) (choice coordinate) *
              entry coordinate (choice coordinate)) := by
      apply Finset.sum_congr rfl
      intro choice _
      simp only [binaryWalshCharacterIn, binaryProductColumn]
      exact Finset.prod_mul_distrib.symm
    _ = ∏ coordinate : Fin width,
        ∑ bit : Fin 2,
          (binaryWalshEntryIn (selected coordinate) bit *
            entry coordinate bit) := by
      exact (Fintype.prod_sum
        (fun coordinate : Fin width => fun bit : Fin 2 =>
          (binaryWalshEntryIn (selected coordinate) bit *
            entry coordinate bit))).symm
    _ = ∏ coordinate : Fin width,
        if selected coordinate = 1 then
          entry coordinate 0 - entry coordinate 1
        else entry coordinate 0 + entry coordinate 1 := by
      apply Finset.prod_congr rfl
      intro coordinate _
      rw [Fin.sum_univ_two]
      generalize selected coordinate = selectedBit
      fin_cases selectedBit <;>
        simp [binaryWalshEntryIn, sub_eq_add_neg]

end KLocality
