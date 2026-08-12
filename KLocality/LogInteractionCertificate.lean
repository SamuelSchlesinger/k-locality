import KLocality.NoLatent
import KLocality.SelectorTrade

namespace KLocality

open scoped BigOperators

universe u

/-!
# Full-support log-interaction certificates

Support leakage cannot detect a full-support target.  The weight-sensitive
analogue is a signed direction in the kernel of the degree-`k` moment map.
Such a direction annihilates every degree-`k` log-density.  A nonzero pairing
with the target log-probabilities is therefore an exact lower-bound
certificate for zero-latent localization.
-/

/-- Every moment-kernel direction is orthogonal to every canonical
degree-`k` feature polynomial. -/
theorem sum_direction_mul_featureEval_eq_zero_of_mem_momentMap_ker
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {direction : Assignment Var → ℝ}
    (hKernel : direction ∈
      LinearMap.ker (FeaturePolynomial.momentMap k))
    (polynomial : FeaturePolynomial Var k) :
    ∑ assignment : Assignment Var,
      direction assignment * polynomial.eval assignment = 0 := by
  unfold FeaturePolynomial.eval
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scope _
  have hScope :
      ∑ assignment : Assignment Var,
        direction assignment * monomialValue scope.1 assignment = 0 := by
    have hAtScope := congrFun hKernel scope
    rw [FeaturePolynomial.momentMap_apply] at hAtScope
    simpa using hAtScope
  calc
    (∑ assignment : Assignment Var,
        direction assignment *
          (polynomial scope * monomialValue scope.1 assignment)) =
        polynomial scope * ∑ assignment : Assignment Var,
          direction assignment * monomialValue scope.1 assignment := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro assignment _
      ring
    _ = 0 := by rw [hScope, mul_zero]

/-- A weight-sensitive obstruction to a full-support degree-`k` Gibbs law. -/
structure LogInteractionCertificate
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) where
  direction : Assignment Var → ℝ
  momentKernel : direction ∈
    LinearMap.ker (FeaturePolynomial.momentMap k)
  detectsLogDensity :
    (∑ assignment : Assignment Var,
      direction assignment * Real.log (p assignment).toReal) ≠ 0

/-- A log-interaction certificate rules out degree-`k` locality on full
support. -/
theorem LogInteractionCertificate.not_isKLocalMarginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p : Distribution (Assignment Var)}
    (certificate : LogInteractionCertificate k p)
    (hFullSupport : p.support = Set.univ) :
    ¬IsKLocalMarginal k p := by
  intro hLocal
  rcases (isKLocalMarginal_iff_fullSupport_logDensity
      k p hFullSupport).1 hLocal with ⟨polynomial, hLogDensity⟩
  apply certificate.detectsLogDensity
  calc
    (∑ assignment : Assignment Var,
        certificate.direction assignment * Real.log (p assignment).toReal) =
        ∑ assignment : Assignment Var,
          certificate.direction assignment * polynomial.eval assignment := by
      apply Finset.sum_congr rfl
      intro assignment _
      rw [hLogDensity assignment]
    _ = 0 :=
      sum_direction_mul_featureEval_eq_zero_of_mem_momentMap_ker
        certificate.momentKernel polynomial

/-- In the paper's range `k ≥ 2`, a full-support log-interaction certificate
gives a strict zero-latent localization lower bound. -/
theorem LogInteractionCertificate.localizationComplexity_pos
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (hk : 2 ≤ k) {p : Distribution (Assignment Var)}
    (certificate : LogInteractionCertificate k p)
    (hFullSupport : p.support = Set.univ) :
    0 < localizationComplexity k Var p := by
  apply Nat.pos_of_ne_zero
  intro hZero
  exact certificate.not_isKLocalMarginal hFullSupport
    ((localizationComplexity_eq_zero_iff_isKLocalMarginal
      hk p).1 hZero)

/-- Exact rational presentation of the moment-kernel half of a
log-interaction certificate.  Only the final nonvanishing statement involves
real logarithms; in concrete rational tables it can be discharged by an
exact multiplicative identity or inequality. -/
structure RationalLogInteractionCertificate
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) where
  direction : Assignment Var → ℚ
  momentBalance : ∀ scope : FeatureScope Var k,
    ∑ assignment : Assignment Var,
      direction assignment * rationalMonomialValue scope.1 assignment = 0
  detectsLogDensity :
    (∑ assignment : Assignment Var,
      (direction assignment : ℝ) * Real.log (p assignment).toReal) ≠ 0

namespace RationalLogInteractionCertificate

/-- Real embedding of a rational log-interaction certificate. -/
noncomputable def toLogInteractionCertificate
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p : Distribution (Assignment Var)}
    (certificate : RationalLogInteractionCertificate k p) :
    LogInteractionCertificate k p where
  direction := fun assignment => certificate.direction assignment
  momentKernel := by
    rw [LinearMap.mem_ker]
    funext scope
    rw [FeaturePolynomial.momentMap_apply]
    have hBalance := congrArg (fun value : ℚ => (value : ℝ))
      (certificate.momentBalance scope)
    simpa [Rat.cast_sum] using hBalance
  detectsLogDensity := certificate.detectsLogDensity

theorem not_isKLocalMarginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p : Distribution (Assignment Var)}
    (certificate : RationalLogInteractionCertificate k p)
    (hFullSupport : p.support = Set.univ) :
    ¬IsKLocalMarginal k p :=
  certificate.toLogInteractionCertificate.not_isKLocalMarginal hFullSupport

theorem localizationComplexity_pos
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (hk : 2 ≤ k) {p : Distribution (Assignment Var)}
    (certificate : RationalLogInteractionCertificate k p)
    (hFullSupport : p.support = Set.univ) :
    0 < localizationComplexity k Var p :=
  certificate.toLogInteractionCertificate.localizationComplexity_pos
    hk hFullSupport

end RationalLogInteractionCertificate

end KLocality
