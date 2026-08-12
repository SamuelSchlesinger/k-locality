import KLocality.FacialSupport

namespace KLocality

open scoped BigOperators

/-!
# Boolean weight tilts

For a Boolean function `f`, its two-level tilt is the full-support rational
law with unnormalized weight `1` on false inputs and `2` on true inputs.
This is the bounded-precision target whose localization complexity can be
compared directly with the circuit complexity of `f`.
-/

/-- Unnormalized rational weight `2 ^ f(x)`, written without coercing a
Boolean exponent. -/
def booleanTiltUnnormalizedRat
    {n : Nat} (f : BitVec n → Bool) (x : BitVec n) : ℚ :=
  if f x then 2 else 1

noncomputable def booleanTiltNormalizerRat
    {n : Nat} (f : BitVec n → Bool) : ℚ :=
  ∑ x : BitVec n, booleanTiltUnnormalizedRat f x

theorem booleanTiltUnnormalizedRat_pos
    {n : Nat} (f : BitVec n → Bool) (x : BitVec n) :
    0 < booleanTiltUnnormalizedRat f x := by
  simp only [booleanTiltUnnormalizedRat]
  split <;> norm_num

theorem booleanTiltNormalizerRat_pos
    {n : Nat} (f : BitVec n → Bool) :
    0 < booleanTiltNormalizerRat f := by
  classical
  unfold booleanTiltNormalizerRat
  exact Finset.sum_pos
    (fun x _ => booleanTiltUnnormalizedRat_pos f x)
    Finset.univ_nonempty

noncomputable def booleanTiltWeightsRat
    {n : Nat} (f : BitVec n → Bool) (x : BitVec n) : ℚ :=
  booleanTiltUnnormalizedRat f x / booleanTiltNormalizerRat f

theorem booleanTiltWeightsRat_pos
    {n : Nat} (f : BitVec n → Bool) (x : BitVec n) :
    0 < booleanTiltWeightsRat f x :=
  div_pos (booleanTiltUnnormalizedRat_pos f x)
    (booleanTiltNormalizerRat_pos f)

theorem sum_booleanTiltWeightsRat
    {n : Nat} (f : BitVec n → Bool) :
    (∑ x : BitVec n, booleanTiltWeightsRat f x) = 1 := by
  classical
  unfold booleanTiltWeightsRat booleanTiltNormalizerRat
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos
    (fun x _ => booleanTiltUnnormalizedRat_pos f x)
    Finset.univ_nonempty))

noncomputable def booleanTiltWeights
    {n : Nat} (f : BitVec n → Bool) (x : BitVec n) : ℝ :=
  booleanTiltWeightsRat f x

/-- The common probability of every false input. -/
noncomputable def booleanTiltLowWeight
    {n : Nat} (f : BitVec n → Bool) : ℝ :=
  ((1 / booleanTiltNormalizerRat f : ℚ) : ℝ)

/-- The common probability of every true input. -/
noncomputable def booleanTiltHighWeight
    {n : Nat} (f : BitVec n → Bool) : ℝ :=
  ((2 / booleanTiltNormalizerRat f : ℚ) : ℝ)

theorem booleanTiltLowWeight_pos
    {n : Nat} (f : BitVec n → Bool) :
    0 < booleanTiltLowWeight f := by
  exact Rat.cast_pos.mpr (div_pos zero_lt_one (booleanTiltNormalizerRat_pos f))

theorem booleanTiltHighWeight_pos
    {n : Nat} (f : BitVec n → Bool) :
    0 < booleanTiltHighWeight f := by
  exact Rat.cast_pos.mpr (div_pos (by norm_num) (booleanTiltNormalizerRat_pos f))

@[simp]
theorem booleanTiltWeights_of_false
    {n : Nat} {f : BitVec n → Bool} {x : BitVec n}
    (hx : f x = false) :
    booleanTiltWeights f x = booleanTiltLowWeight f := by
  simp [booleanTiltWeights, booleanTiltWeightsRat, booleanTiltLowWeight,
    booleanTiltUnnormalizedRat, hx]

@[simp]
theorem booleanTiltWeights_of_true
    {n : Nat} {f : BitVec n → Bool} {x : BitVec n}
    (hx : f x = true) :
    booleanTiltWeights f x = booleanTiltHighWeight f := by
  simp [booleanTiltWeights, booleanTiltWeightsRat, booleanTiltHighWeight,
    booleanTiltUnnormalizedRat, hx]

/-- The full-support rational distribution
`D_f(x) = 2 ^ f(x) / ∑_y 2 ^ f(y)`. -/
noncomputable def booleanTiltDistribution
    {n : Nat} (f : BitVec n → Bool) : Distribution (BitVec n) :=
  distributionOfRealWeights (booleanTiltWeights f)
    (fun x => Rat.cast_nonneg.mpr (booleanTiltWeightsRat_pos f x).le)
    (by
      have hCast := congrArg (fun value : ℚ => (value : ℝ))
        (sum_booleanTiltWeightsRat f)
      simpa [booleanTiltWeights, Rat.cast_sum] using hCast)

@[simp]
theorem booleanTiltDistribution_apply_toReal
    {n : Nat} (f : BitVec n → Bool) (x : BitVec n) :
    (booleanTiltDistribution f x).toReal = booleanTiltWeights f x := by
  exact distributionOfRealWeights_apply_toReal _ _ _ x

theorem booleanTiltDistribution_support
    {n : Nat} (f : BitVec n → Bool) :
    (booleanTiltDistribution f).support = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff (booleanTiltDistribution f) x).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [booleanTiltDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  exact (ne_of_gt (Rat.cast_pos.mpr (booleanTiltWeightsRat_pos f x))) hReal

@[simp]
theorem booleanTiltUnnormalizedRat_false
    {n : Nat} {f : BitVec n → Bool} {x : BitVec n}
    (hx : f x = false) :
    booleanTiltUnnormalizedRat f x = 1 := by
  simp [booleanTiltUnnormalizedRat, hx]

@[simp]
theorem booleanTiltUnnormalizedRat_true
    {n : Nat} {f : BitVec n → Bool} {x : BitVec n}
    (hx : f x = true) :
    booleanTiltUnnormalizedRat f x = 2 := by
  simp [booleanTiltUnnormalizedRat, hx]

end KLocality
