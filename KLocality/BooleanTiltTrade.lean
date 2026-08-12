import KLocality.BooleanTiltCircuit
import KLocality.LatentPadding
import KLocality.MarginalTradeCertificate

namespace KLocality

open scoped BigOperators

/-!
# Marginal trades evaluated on Boolean tilts

For the full-support tilt `D_f(x) proportional to 2 ^ f(x)`, every
homogeneous marginal-trade identity loses its common normalization factor.
What remains is an equality between finite sums of powers of two.  Thus a
trade certificate can be checked using natural-number arithmetic alone.

Combined with `BooleanTiltCircuit`, a family of unequal trade codes gives a
literal lower bound for the NAND circuit complexity of `f`.
-/

/-- The number of tuple entries on which `f` is true. -/
def booleanTiltTrueCount
    {n degree : Nat} (f : BitVec n -> Bool)
    (tuple : Fin degree -> BitVec n) : Nat :=
  ∑ index : Fin degree, if f (tuple index) then 1 else 0

/-- The product of unnormalized Boolean-tilt weights is a power of two. -/
theorem prod_booleanTiltUnnormalizedRat
    {n degree : Nat} (f : BitVec n -> Bool)
    (tuple : Fin degree -> BitVec n) :
    (∏ index : Fin degree, booleanTiltUnnormalizedRat f (tuple index)) =
      (2 : ℚ) ^ booleanTiltTrueCount f tuple := by
  classical
  calc
    (∏ index : Fin degree, booleanTiltUnnormalizedRat f (tuple index)) =
        ∏ index : Fin degree,
          (2 : ℚ) ^ (if f (tuple index) then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro index _
      cases hValue : f (tuple index) <;>
        simp [booleanTiltUnnormalizedRat, hValue]
    _ = (2 : ℚ) ^ booleanTiltTrueCount f tuple := by
      simpa [booleanTiltTrueCount] using
        Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin degree))
          (fun index => if f (tuple index) then 1 else 0) (2 : ℚ)

/-- A normalized Boolean-tilt weight is its common low weight times its
unnormalized value. -/
theorem booleanTiltWeights_eq_low_mul_unnormalized
    {n : Nat} (f : BitVec n -> Bool) (x : BitVec n) :
    booleanTiltWeights f x = booleanTiltLowWeight f *
      (booleanTiltUnnormalizedRat f x : ℝ) := by
  unfold booleanTiltWeights booleanTiltWeightsRat booleanTiltLowWeight
  push_cast
  field_simp [ne_of_gt (booleanTiltNormalizerRat_pos f)]

/-- Each visible tuple monomial is a common normalization power times an
integer power of two. -/
theorem prod_booleanTiltWeights
    {n degree : Nat} (f : BitVec n -> Bool)
    (tuple : Fin degree -> BitVec n) :
    (∏ index : Fin degree, booleanTiltWeights f (tuple index)) =
      (booleanTiltLowWeight f) ^ degree *
        ((2 ^ booleanTiltTrueCount f tuple : Nat) : ℝ) := by
  classical
  simp_rw [booleanTiltWeights_eq_low_mul_unnormalized]
  rw [Finset.prod_mul_distrib]
  have hProductRat := prod_booleanTiltUnnormalizedRat f tuple
  have hProductReal := congrArg (fun value : ℚ => (value : ℝ)) hProductRat
  rw [show (∏ _index : Fin degree, booleanTiltLowWeight f) =
      booleanTiltLowWeight f ^ degree by simp]
  rw [show (∏ index : Fin degree,
      (booleanTiltUnnormalizedRat f (tuple index) : ℝ)) =
        ((2 ^ booleanTiltTrueCount f tuple : Nat) : ℝ) by
    simpa [Rat.cast_prod, Rat.cast_pow, Nat.cast_pow] using hProductReal]

namespace MarginalTradeCertificate

/-- Natural-number code obtained by evaluating the positive trade terms at
the unnormalized weights `2 ^ f(x)`. -/
def booleanTiltPositiveCode
    {k degree termCount n latentBits : Nat}
    (certificate : MarginalTradeCertificate
      k degree termCount (Fin n) (Fin latentBits))
    (f : BitVec n -> Bool) : Nat :=
  ∑ term : Fin termCount,
    2 ^ booleanTiltTrueCount f (certificate.positive term)

/-- Natural-number code obtained by evaluating the negative trade terms at
the unnormalized weights `2 ^ f(x)`. -/
def booleanTiltNegativeCode
    {k degree termCount n latentBits : Nat}
    (certificate : MarginalTradeCertificate
      k degree termCount (Fin n) (Fin latentBits))
    (f : BitVec n -> Bool) : Nat :=
  ∑ term : Fin termCount,
    2 ^ booleanTiltTrueCount f (certificate.negative term)

/-- Evaluation of the positive side factors into a common normalizer and a
natural-number code. -/
theorem positiveValue_booleanTiltWeights
    {k degree termCount n latentBits : Nat}
    (certificate : MarginalTradeCertificate
      k degree termCount (Fin n) (Fin latentBits))
    (f : BitVec n -> Bool) :
    certificate.positiveValue (booleanTiltWeights f) =
      (booleanTiltLowWeight f) ^ degree *
        (certificate.booleanTiltPositiveCode f : ℝ) := by
  classical
  unfold positiveValue booleanTiltPositiveCode
  simp_rw [prod_booleanTiltWeights]
  push_cast
  rw [Finset.mul_sum]

/-- Evaluation of the negative side factors into the same common normalizer
and a natural-number code. -/
theorem negativeValue_booleanTiltWeights
    {k degree termCount n latentBits : Nat}
    (certificate : MarginalTradeCertificate
      k degree termCount (Fin n) (Fin latentBits))
    (f : BitVec n -> Bool) :
    certificate.negativeValue (booleanTiltWeights f) =
      (booleanTiltLowWeight f) ^ degree *
        (certificate.booleanTiltNegativeCode f : ℝ) := by
  classical
  unfold negativeValue booleanTiltNegativeCode
  simp_rw [prod_booleanTiltWeights]
  push_cast
  rw [Finset.mul_sum]

/-- A trade detects `D_f` exactly when its two natural-number codes differ. -/
theorem value_ne_booleanTiltWeights_iff_code_ne
    {k degree termCount n latentBits : Nat}
    (certificate : MarginalTradeCertificate
      k degree termCount (Fin n) (Fin latentBits))
    (f : BitVec n -> Bool) :
    certificate.positiveValue (booleanTiltWeights f) ≠
        certificate.negativeValue (booleanTiltWeights f) ↔
      certificate.booleanTiltPositiveCode f ≠
        certificate.booleanTiltNegativeCode f := by
  rw [certificate.positiveValue_booleanTiltWeights,
    certificate.negativeValue_booleanTiltWeights]
  constructor
  · intro hValues hCodes
    exact hValues (by rw [hCodes])
  · intro hCodes hValues
    have hFactor : (booleanTiltLowWeight f : ℝ) ^ degree ≠ 0 :=
      ne_of_gt (pow_pos (booleanTiltLowWeight_pos f) degree)
    have hCasts : (certificate.booleanTiltPositiveCode f : ℝ) =
        certificate.booleanTiltNegativeCode f :=
      mul_left_cancel₀ hFactor hValues
    exact hCodes (by exact_mod_cast hCasts)

/-- Unequal natural-number trade codes rule out the prescribed localization
of the full-support rational tilt. -/
theorem obstructs_booleanTilt_of_code_ne
    {k degree termCount n latentBits : Nat}
    (certificate : MarginalTradeCertificate
      k degree termCount (Fin n) (Fin latentBits))
    (f : BitVec n -> Bool)
    (hCodes : certificate.booleanTiltPositiveCode f ≠
      certificate.booleanTiltNegativeCode f) :
    ¬HasKLocalizationBits k latentBits n (booleanTiltDistribution f) := by
  apply certificate.obstructs_localization
  simpa only [booleanTiltDistribution_apply_toReal] using
    (certificate.value_ne_booleanTiltWeights_iff_code_ne f).2 hCodes

/-- A family of finite code inequalities proves a localization-complexity
lower bound for a Boolean tilt. -/
theorem localizationComplexityBits_gt_of_booleanTiltTradeCodes
    {k n budget : Nat} (hk : 2 ≤ k) (f : BitVec n -> Bool)
    (certificates : ∀ latentBits, latentBits ≤ budget ->
      ∃ degree termCount,
        ∃ certificate : MarginalTradeCertificate
          k degree termCount (Fin n) (Fin latentBits),
          certificate.booleanTiltPositiveCode f ≠
            certificate.booleanTiltNegativeCode f) :
    budget < localizationComplexityBits k n (booleanTiltDistribution f) := by
  apply localizationComplexity_gt_of_tradeCertificates hk
  intro latentBits hLatent
  rcases certificates latentBits hLatent with
    ⟨degree, termCount, certificate, hCodes⟩
  have hValues :
      certificate.positiveValue
          (fun x => ((booleanTiltDistribution f) x).toReal) ≠
        certificate.negativeValue
          (fun x => ((booleanTiltDistribution f) x).toReal) := by
    simpa only [booleanTiltDistribution_apply_toReal] using
      (certificate.value_ne_booleanTiltWeights_iff_code_ne f).2 hCodes
  exact ⟨degree, termCount, certificate, hValues⟩

end MarginalTradeCertificate

/-- A family of order-three marginal trades whose integer codes differ gives
a NAND circuit lower bound for the underlying Boolean function.  This is the
full-support distribution-to-circuit transfer theorem. -/
theorem NANDCircuit.CNAND_gt_of_booleanTiltTradeCodes
    {n budget : Nat} (f : BitVec n -> Bool)
    (hCircuitExists : ∃ gateCount,
      NANDCircuit.NANDRecognizerWitness n
        (NANDCircuit.booleanTrueInputs f) gateCount)
    (certificates : ∀ latentBits, latentBits ≤ budget ->
      ∃ degree termCount,
        ∃ certificate : MarginalTradeCertificate
          3 degree termCount (Fin n) (Fin latentBits),
          certificate.booleanTiltPositiveCode f ≠
            certificate.booleanTiltNegativeCode f) :
    budget < NANDCircuit.CNAND n
      (NANDCircuit.booleanTrueInputs f) hCircuitExists := by
  have hLocalization :=
    MarginalTradeCertificate.localizationComplexityBits_gt_of_booleanTiltTradeCodes
      (k := 3) (by norm_num) f certificates
  have hCircuitUpper :=
    NANDCircuit.localizationComplexityBits_three_booleanTilt_le_CNAND
      f hCircuitExists
  exact lt_of_lt_of_le hLocalization hCircuitUpper

/-- A trade cannot separate the Boolean tilt of a function whose supplied
NAND circuit already fits within the trade's hidden-bit budget.  This is the
formal sanity check behind the explicitness barrier: a proposed simple test
cannot acquire a larger circuit lower bound merely by choosing a clever
marginal trade. -/
theorem MarginalTradeCertificate.booleanTiltCodes_eq_of_nandCircuit_le
    {degree termCount n gateCount latentBits : Nat}
    (certificate : MarginalTradeCertificate
      3 degree termCount (Fin n) (Fin latentBits))
    (f : BitVec n -> Bool)
    (recognizer : NANDCircuit.Recognizer n gateCount)
    (hComputes : recognizer.eval = f)
    (hGateCount : gateCount ≤ latentBits) :
    certificate.booleanTiltPositiveCode f =
      certificate.booleanTiltNegativeCode f := by
  by_contra hCodes
  have hNoLocalization := certificate.obstructs_booleanTilt_of_code_ne f hCodes
  have hSmallLocalization :=
    recognizer.hasThreeLocalization_booleanTilt_of_computes hComputes
  exact hNoLocalization
    (hasKLocalizationBits_padLatent (by norm_num) hGateCount hSmallLocalization)

end KLocality
