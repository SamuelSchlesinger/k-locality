import KLocality.LogInteractionCertificate
import KLocality.SelectorTradeExample

namespace KLocality

open scoped BigOperators

/-!
# A rational full-support localization lower bound

This is the manuscript's first marginal-ideal example, proved directly from
the alternating three-cube interaction.  The distribution assigns probability
`2/9` to `111` and `1/9` to every other point.  It has full support, but its
log-density has a nonzero cubic interaction, so it is not quadratically local
without latent bits.
-/

/-- Coordinate enumeration of the three-cube. -/
def bitVecThreeEquiv : BitVec 3 ≃ Bool × Bool × Bool where
  toFun assignment := (assignment 0, assignment 1, assignment 2)
  invFun bits := ![bits.1, bits.2.1, bits.2.2]
  left_inv assignment := by
    funext coordinate
    fin_cases coordinate <;> rfl
  right_inv bits := by
    rcases bits with ⟨first, second, third⟩
    rfl

/-- The all-true point of the three-cube. -/
def allTrueThree : BitVec 3 := fun _ => true

/-- Probability table with weight two at `111` and weight one elsewhere. -/
noncomputable def boostedThreeWeights (assignment : BitVec 3) : ℝ :=
  if assignment = allTrueThree then 2 / 9 else 1 / 9

/-- The rational full-support PMF used by the first marginal-ideal
certificate in the manuscript. -/
noncomputable def boostedThreeDistribution : Distribution (BitVec 3) :=
  distributionOfRealWeights boostedThreeWeights
    (by
      intro assignment
      simp only [boostedThreeWeights]
      split <;> norm_num)
    (by
      classical
      calc
        (∑ assignment : BitVec 3, boostedThreeWeights assignment) =
            ∑ assignment : BitVec 3, ((1 / 9 : ℝ) +
              if assignment = allTrueThree then 1 / 9 else 0) := by
          apply Finset.sum_congr rfl
          intro assignment _
          by_cases hAssignment : assignment = allTrueThree
          · simp [boostedThreeWeights, hAssignment]
            norm_num
          · simp [boostedThreeWeights, hAssignment]
        _ = (Fintype.card (BitVec 3) : ℝ) * (1 / 9) + 1 / 9 := by
          rw [Finset.sum_add_distrib]
          simp
        _ = 1 := by
          norm_num [BitVec, Fintype.card_fun]
          rfl)

@[simp]
theorem boostedThreeDistribution_apply_toReal (assignment : BitVec 3) :
    (boostedThreeDistribution assignment).toReal =
      boostedThreeWeights assignment := by
  exact distributionOfRealWeights_apply_toReal _ _ _ assignment

/-- Rational alternating sign on the three-cube. -/
def parityDirectionRat (assignment : BitVec 3) : ℚ :=
  if parityThree assignment = false then 1 else -1

/-- Real embedding of the alternating sign. -/
noncomputable def parityDirection (assignment : BitVec 3) : ℝ :=
  parityDirectionRat assignment

/-- The alternating three-cube trade annihilates every monomial of degree at
most two.  This finite rational identity is checked by kernel reduction. -/
theorem parityDirectionRat_momentBalance :
    ∀ scope : FeatureScope (Fin 3) 2,
      ∑ assignment : BitVec 3,
        parityDirectionRat assignment *
          rationalMonomialValue scope.1 assignment = 0 := by
  native_decide

/-- Hence the alternating functional annihilates every quadratic canonical
pseudo-Boolean polynomial. -/
theorem parityDirection_annihilates_quadratic
    (polynomial : FeaturePolynomial (Fin 3) 2) :
    ∑ assignment : BitVec 3,
      parityDirection assignment * polynomial.eval assignment = 0 := by
  unfold FeaturePolynomial.eval
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scope _
  have hRational := congrArg (fun value : ℚ => (value : ℝ))
    (parityDirectionRat_momentBalance scope)
  have hScope :
      ∑ assignment : BitVec 3,
        parityDirection assignment * monomialValue scope.1 assignment = 0 := by
    simpa [parityDirection, Rat.cast_sum] using hRational
  calc
    (∑ assignment : BitVec 3,
        parityDirection assignment *
          (polynomial scope * monomialValue scope.1 assignment)) =
        polynomial scope * ∑ assignment : BitVec 3,
          parityDirection assignment * monomialValue scope.1 assignment := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro assignment _
      ring
    _ = 0 := by rw [hScope, mul_zero]

/-- The same alternating functional detects a nonzero three-way interaction
in the log-probability table. -/
theorem boostedThree_alternating_log_sum :
    (∑ assignment : BitVec 3,
      parityDirection assignment * Real.log (boostedThreeWeights assignment)) =
        Real.log (1 / 9) - Real.log (2 / 9) := by
  have h111 : (![true, true, true] : BitVec 3) = allTrueThree := by
    native_decide
  have h110 : (![true, true, false] : BitVec 3) ≠ allTrueThree := by
    native_decide
  have h101 : (![true, false, true] : BitVec 3) ≠ allTrueThree := by
    native_decide
  have h100 : (![true, false, false] : BitVec 3) ≠ allTrueThree := by
    native_decide
  have h011 : (![false, true, true] : BitVec 3) ≠ allTrueThree := by
    native_decide
  have h010 : (![false, true, false] : BitVec 3) ≠ allTrueThree := by
    native_decide
  have h001 : (![false, false, true] : BitVec 3) ≠ allTrueThree := by
    native_decide
  have h000 : (![false, false, false] : BitVec 3) ≠ allTrueThree := by
    native_decide
  rw [← bitVecThreeEquiv.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp [bitVecThreeEquiv, parityDirection, parityDirectionRat, parityThree,
    boostedThreeWeights, h111, h110, h101, h100, h011, h010, h001, h000,
    allTrueThree]
  ring

/-- The example is strictly positive at every cube point. -/
theorem boostedThree_support :
    boostedThreeDistribution.support = Set.univ := by
  ext assignment
  simp only [Set.mem_univ, iff_true]
  apply (PMF.mem_support_iff boostedThreeDistribution assignment).2
  intro hZero
  have hReal := congrArg ENNReal.toReal hZero
  rw [boostedThreeDistribution_apply_toReal] at hReal
  simp only [ENNReal.toReal_zero] at hReal
  have hPositive : 0 < boostedThreeWeights assignment := by
    simp only [boostedThreeWeights]
    split <;> norm_num
  exact (ne_of_gt hPositive) hReal

/-- The rational alternating direction, packaged as a reusable
log-interaction certificate. -/
noncomputable def boostedThreeLogInteractionCertificate :
    RationalLogInteractionCertificate 2 boostedThreeDistribution where
  direction := parityDirectionRat
  momentBalance := parityDirectionRat_momentBalance
  detectsLogDensity := by
    intro hZero
    have hTable :
        (∑ assignment : BitVec 3,
          (parityDirectionRat assignment : ℝ) *
            Real.log (boostedThreeDistribution assignment).toReal) =
          Real.log (1 / 9) - Real.log (2 / 9) := by
      calc
        _ = ∑ assignment : BitVec 3,
            parityDirection assignment *
              Real.log (boostedThreeWeights assignment) := by
          apply Finset.sum_congr rfl
          intro assignment _
          rw [boostedThreeDistribution_apply_toReal]
          rfl
        _ = _ := boostedThree_alternating_log_sum
    rw [hTable] at hZero
    have hLogNe : Real.log (1 / 9 : ℝ) ≠ Real.log (2 / 9 : ℝ) := by
      intro hEqual
      have hNumbers : (1 / 9 : ℝ) = 2 / 9 :=
        Real.log_injOn_pos (by norm_num) (by norm_num) hEqual
      norm_num at hNumbers
    exact hLogNe (sub_eq_zero.mp hZero)

/-- The rational full-support table is not a quadratic Gibbs law. -/
theorem boostedThree_not_twoLocal :
    ¬IsKLocalMarginal 2 boostedThreeDistribution := by
  exact boostedThreeLogInteractionCertificate.not_isKLocalMarginal
    boostedThree_support

/-- The manuscript's first explicit marginal-ideal example, stated as a
localization lower bound.  Its full support makes this intrinsically a weight
obstruction rather than a support/circuit obstruction. -/
theorem boostedThree_localizationComplexity_pos :
    0 < localizationComplexityBits 2 3 boostedThreeDistribution := by
  exact boostedThreeLogInteractionCertificate.localizationComplexity_pos
    le_rfl boostedThree_support

end KLocality
