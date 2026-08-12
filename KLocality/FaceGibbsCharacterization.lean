import KLocality.GibbsOptimality
import KLocality.MarginalPolytope

namespace KLocality

open scoped BigOperators

universe u

/-!
# Paper-facing face--Gibbs characterization

The lower-level theorem `isKLocalMarginal_iff_isFaceGibbs` uses an exposing
polynomial and a log-density as compact certificates.  This file identifies
that certificate with an actual exposed face of `marginalPolytope` and states
the normalized Gibbs formula exactly as it appears in the manuscript.
-/

/-- Literal finite marginal-polytope face plus normalized Gibbs density. -/
def IsMarginalPolytopeFaceGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) : Prop :=
  ∃ (face : Set (FeatureVector Var k))
      (theta : FeaturePolynomial Var k),
    IsExposed ℝ (marginalPolytope k) face ∧
      p.support = canonicalFeature k ⁻¹' face ∧
        ∀ x ∈ p.support,
          (p x).toReal = Real.exp (theta.eval x) /
            ∑ z ∈ UniversalExistence.supportFinset p,
              Real.exp (theta.eval z)

/-- **Theorem `thm:face-gibbs`.** A distribution on a finite Boolean cube is
`k`-local iff its support is the inverse image of an exposed face of the
order-`k` marginal polytope and, on that support, it is a normalized Gibbs law
with a degree-`k` canonical feature polynomial. -/
theorem isKLocalMarginal_iff_marginalPolytopeFaceGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    IsKLocalMarginal k p ↔ IsMarginalPolytopeFaceGibbs k p := by
  classical
  constructor
  · intro hLocal
    have hCertificate := (isKLocalMarginal_iff_isFaceGibbs k p).1 hLocal
    rcases hCertificate with ⟨hFacial, theta, hLog⟩
    rcases exists_exposedFace_preimage_of_isFacialSupport
        p.support_nonempty hFacial with ⟨face, hExposed, hSupport⟩
    refine ⟨face, theta, hExposed, hSupport, ?_⟩
    intro x hx
    simpa [featurePartition] using
      normalized_gibbs_formula_of_logDensity p theta hLog x hx
  · rintro ⟨face, theta, hExposed, hSupport, hFormula⟩
    have hFacial : IsFacialSupport k p.support :=
      isFacialSupport_of_exists_exposedFace_preimage p.support_nonempty
        ⟨face, hExposed, hSupport⟩
    let partition : ℝ :=
      ∑ z ∈ UniversalExistence.supportFinset p, Real.exp (theta.eval z)
    have hSupportFinsetNonempty :
        (UniversalExistence.supportFinset p).Nonempty := by
      rcases p.support_nonempty with ⟨x, hx⟩
      exact ⟨x, (UniversalExistence.mem_supportFinset p x).2 hx⟩
    have hPartitionPos : 0 < partition := by
      apply Finset.sum_pos
      · intro x _
        exact Real.exp_pos _
      · exact hSupportFinsetNonempty
    let adjustedTheta : FeaturePolynomial Var k :=
      theta - FeaturePolynomial.constant k (Real.log partition)
    have hAdjustedLog : ∀ x ∈ p.support,
        Real.log (p x).toReal = adjustedTheta.eval x := by
      intro x hx
      have hAtX := hFormula x hx
      change (p x).toReal = Real.exp (theta.eval x) / partition at hAtX
      rw [hAtX, Real.log_div (Real.exp_pos _).ne' hPartitionPos.ne',
        Real.log_exp]
      simp [adjustedTheta]
    exact isKLocalMarginal_of_isFaceGibbs k p
      ⟨hFacial, adjustedTheta, hAdjustedLog⟩

/-- **Corollary `cor:ground-state`.** Every `k`-local law has support equal to
the zero set of a nonnegative multilinear Boolean polynomial of degree at most
`k`. -/
theorem exists_nonnegative_featurePolynomial_zeroSet_of_isKLocalMarginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hLocal : IsKLocalMarginal k p) :
    ∃ energy : FeaturePolynomial Var k,
      (∀ x, 0 ≤ energy.eval x) ∧
        ∀ x, energy.eval x = 0 ↔ x ∈ p.support :=
  isFacialSupport_of_isKLocalMarginal k p hLocal

end KLocality
