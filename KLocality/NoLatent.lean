import KLocality.Reindex
import KLocality.UniversalExistence

namespace KLocality

open scoped BigOperators

universe u

/-!
# Zero latent variables and full-support Gibbs laws

The type `Fin 0` has no latent coordinates, but the joint variable type is
still syntactically `ObsVar ⊕ Fin 0`.  Reindexing along `Equiv.sumEmpty`
removes that bookkeeping and identifies zero-bit localizations with local laws
on the observed cube itself.
-/

/-- Coordinate equivalence which forgets the impossible `Fin 0` summand. -/
def noLatentCoordinateEquiv (ObsVar : Type u) :
    Sum ObsVar (Fin 0) ≃ ObsVar :=
  Equiv.sumEmpty ObsVar (Fin 0)

theorem projectObs_eq_assignmentEquiv_noLatent
    (ObsVar : Type u) :
    (projectObs : Assignment (Sum ObsVar (Fin 0)) → Assignment ObsVar) =
      assignmentEquiv (noLatentCoordinateEquiv ObsVar) := by
  funext assignment coordinate
  rfl

/-- A localization with zero latent bits is exactly a local law on the
observed coordinates. -/
theorem hasKLocalization_zero_iff_isKLocalMarginal
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (k : Nat) (p : Distribution (Assignment ObsVar)) :
    HasKLocalization k 0 ObsVar p ↔ IsKLocalMarginal k p := by
  let equiv := noLatentCoordinateEquiv ObsVar
  constructor
  · rintro ⟨localization⟩
    have hMarginal : reindexDistribution equiv localization.lifted = p := by
      change localization.lifted.map (assignmentEquiv equiv) = p
      rw [← projectObs_eq_assignmentEquiv_noLatent ObsVar]
      exact localization.marginal
    have hRenamed : IsKLocalMarginal k
        (reindexDistribution equiv localization.lifted) :=
      (isKLocalMarginal_reindexDistribution_iff equiv k localization.lifted).2
        localization.kLocal
    rwa [hMarginal] at hRenamed
  · intro hLocal
    let lifted := reindexDistribution equiv.symm p
    refine ⟨{
      lifted := lifted
      marginal := ?_
      kLocal := ?_ }⟩
    · change lifted.map projectObs = p
      rw [projectObs_eq_assignmentEquiv_noLatent ObsVar]
      change reindexDistribution equiv lifted = p
      exact reindexDistribution_reindexDistribution_symm equiv p
    · exact (isKLocalMarginal_reindexDistribution_iff equiv.symm k p).2 hLocal

/-- In the manuscript's range `k ≥ 2`, localization complexity is zero iff
the observed law itself is `k`-local. -/
theorem localizationComplexity_eq_zero_iff_isKLocalMarginal
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {k : Nat} (hk : 2 ≤ k) (p : Distribution (Assignment ObsVar)) :
    localizationComplexity k ObsVar p = 0 ↔ IsKLocalMarginal k p := by
  constructor
  · intro hZero
    have hSpec := localizationComplexity_spec k ObsVar p
      (kLocalization_exists p hk)
    rw [hZero] at hSpec
    exact (hasKLocalization_zero_iff_isKLocalMarginal k p).1 hSpec
  · intro hLocal
    have hZeroLocalization : HasKLocalization k 0 ObsVar p :=
      (hasKLocalization_zero_iff_isKLocalMarginal k p).2 hLocal
    exact Nat.eq_zero_of_le_zero
      (localizationComplexity_min k ObsVar p 0 hZeroLocalization)

/-- The canonical support finset of a full-support law is the whole Boolean
cube. -/
theorem supportFinset_eq_univ_of_support_eq_univ
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) (hFull : p.support = Set.univ) :
    UniversalExistence.supportFinset p = Finset.univ := by
  ext x
  rw [UniversalExistence.mem_supportFinset]
  simp [hFull]

/-- On full support, `k`-locality is exactly a degree-`k` log-density. -/
theorem isKLocalMarginal_iff_fullSupport_logDensity
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hFull : p.support = Set.univ) :
    IsKLocalMarginal k p ↔
      ∃ theta : FeaturePolynomial Var k,
        ∀ x, Real.log (p x).toReal = theta.eval x := by
  constructor
  · intro hLocal
    rcases isFeatureGibbs_of_isKLocalMarginal k p hLocal with ⟨theta, hLog⟩
    exact ⟨theta, fun x => hLog x (by rw [hFull]; trivial)⟩
  · rintro ⟨theta, hLog⟩
    have hFacial : IsFacialSupport k p.support := by
      let energy : FeaturePolynomial Var k :=
        FeaturePolynomial.constant (Var := Var) k 0
      refine ⟨energy, ?_, ?_⟩
      · intro x
        simp [energy]
      · intro x
        simp [energy, hFull]
    exact isKLocalMarginal_of_isFaceGibbs k p
      ⟨hFacial, theta, fun x _ => hLog x⟩

/-- Full-support version of the displayed normalized Gibbs law. -/
theorem isKLocalMarginal_iff_fullSupport_normalizedGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hFull : p.support = Set.univ) :
    IsKLocalMarginal k p ↔
      ∃ theta : FeaturePolynomial Var k,
        ∀ x,
          (p x).toReal = Real.exp (theta.eval x) /
            ∑ z : Assignment Var, Real.exp (theta.eval z) := by
  classical
  constructor
  · intro hLocal
    rcases isFeatureGibbs_of_isKLocalMarginal k p hLocal with ⟨theta, hLog⟩
    refine ⟨theta, ?_⟩
    intro x
    have hxSupport : x ∈ p.support := by rw [hFull]; trivial
    have hFormula := normalized_gibbs_formula_of_logDensity p theta hLog x hxSupport
    rw [featurePartition,
      supportFinset_eq_univ_of_support_eq_univ p hFull] at hFormula
    exact hFormula
  · rintro ⟨theta, hFormula⟩
    let partition : ℝ := ∑ z : Assignment Var, Real.exp (theta.eval z)
    have hPartitionPos : 0 < partition := by
      apply Finset.sum_pos
      · intro x _
        exact Real.exp_pos _
      · exact Finset.univ_nonempty
    let adjustedTheta : FeaturePolynomial Var k :=
      theta - FeaturePolynomial.constant k (Real.log partition)
    apply (isKLocalMarginal_iff_fullSupport_logDensity k p hFull).2
    refine ⟨adjustedTheta, ?_⟩
    intro x
    have hAtX := hFormula x
    change (p x).toReal = Real.exp (theta.eval x) / partition at hAtX
    rw [hAtX, Real.log_div (Real.exp_pos _).ne' hPartitionPos.ne',
      Real.log_exp]
    simp [adjustedTheta]

/-- **Proposition `prop:positive-no-latent`.** For a full-support law and
`k ≥ 2`, zero localization complexity is equivalent to the normalized Gibbs
form of a multilinear polynomial of degree at most `k`. -/
theorem localizationComplexity_eq_zero_iff_fullSupport_normalizedGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (hk : 2 ≤ k) (p : Distribution (Assignment Var))
    (hFull : p.support = Set.univ) :
    localizationComplexity k Var p = 0 ↔
      ∃ theta : FeaturePolynomial Var k,
        ∀ x,
          (p x).toReal = Real.exp (theta.eval x) /
            ∑ z : Assignment Var, Real.exp (theta.eval z) := by
  rw [localizationComplexity_eq_zero_iff_isKLocalMarginal hk p,
    isKLocalMarginal_iff_fullSupport_normalizedGibbs k p hFull]

end KLocality
