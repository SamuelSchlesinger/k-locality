import KLocality.CoordinateSubstitution

namespace KLocality

universe u v

/-!
# Relative finite Gibbs laws

The source PMF is a free base measure.  A relative Gibbs factor may only add
a degree-bounded facial indicator and an exponential degree-bounded weight on
the source-plus-fresh cube.  We absorb the positive scalar normalizer into the
constant coefficient of the potential.  Thus the displayed formula below is
the paper's `(GR)` formula in the canonical normalization `Z = 1`; shifting
the constant coefficient recovers any positive `Z`.
-/

/-- The nonnegative Gibbs multiplier selected by a facial energy. -/
noncomputable def relativeGibbsFactor
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (energy potential : FeaturePolynomial Var k)
    (assignment : Assignment Var) : ENNReal :=
  if energy.eval assignment = 0 then
    ENNReal.ofReal (Real.exp (potential.eval assignment))
  else 0

theorem relativeGibbsFactor_ne_zero_iff
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (energy potential : FeaturePolynomial Var k)
    (assignment : Assignment Var) :
    relativeGibbsFactor energy potential assignment ≠ 0 ↔
      energy.eval assignment = 0 := by
  classical
  by_cases hEnergy : energy.eval assignment = 0
  · simp [relativeGibbsFactor, hEnergy,
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
  · simp [relativeGibbsFactor, hEnergy]

/-- A relative degree-`k` face--Gibbs extension of a source law.

The potential includes the additive normalization constant, so the formula
has no separate `Z`.  This is equivalent to the manuscript convention because
the constant monomial is present among degree-at-most-`k` features. -/
structure RelativeFaceGibbsCertificate
    (k : Nat)
    {Source : Type u} {Fresh : Type v}
    [Fintype Source] [Fintype Fresh]
    [DecidableEq Source] [DecidableEq Fresh]
    (source : Distribution (Assignment Source))
    (extension : Distribution (Assignment (Sum Source Fresh))) where
  energy : FeaturePolynomial (Sum Source Fresh) k
  energy_nonnegative : ∀ assignment, 0 ≤ energy.eval assignment
  potential : FeaturePolynomial (Sum Source Fresh) k
  probability_eq : ∀ assignment,
    extension assignment =
      source (projectObs assignment) *
        relativeGibbsFactor energy potential assignment

/-- Propositional form of relative face--Gibbs representability. -/
def IsRelativeFaceGibbs
    (k : Nat)
    {Source : Type u} {Fresh : Type v}
    [Fintype Source] [Fintype Fresh]
    [DecidableEq Source] [DecidableEq Fresh]
    (source : Distribution (Assignment Source))
    (extension : Distribution (Assignment (Sum Source Fresh))) : Prop :=
  Nonempty (RelativeFaceGibbsCertificate k source extension)

/-- The relative extension is supported exactly where the source has positive
mass and the exposing energy vanishes. -/
theorem RelativeFaceGibbsCertificate.mem_support_iff
    {Source : Type u} {Fresh : Type v}
    [Fintype Source] [Fintype Fresh]
    [DecidableEq Source] [DecidableEq Fresh]
    {k : Nat}
    {source : Distribution (Assignment Source)}
    {extension : Distribution (Assignment (Sum Source Fresh))}
    (hRelative : RelativeFaceGibbsCertificate k source extension)
    (assignment : Assignment (Sum Source Fresh)) :
    assignment ∈ extension.support ↔
      projectObs assignment ∈ source.support ∧
        hRelative.energy.eval assignment = 0 := by
  rw [PMF.mem_support_iff, hRelative.probability_eq,
    mul_ne_zero_iff, relativeGibbsFactor_ne_zero_iff,
    ← PMF.mem_support_iff]

/-- On relative support, the logarithm splits into the source log weight and
the added local potential. -/
theorem RelativeFaceGibbsCertificate.log_probability_eq
    {Source : Type u} {Fresh : Type v}
    [Fintype Source] [Fintype Fresh]
    [DecidableEq Source] [DecidableEq Fresh]
    {k : Nat}
    {source : Distribution (Assignment Source)}
    {extension : Distribution (Assignment (Sum Source Fresh))}
    (hRelative : RelativeFaceGibbsCertificate k source extension)
    (assignment : Assignment (Sum Source Fresh))
    (hAssignment : assignment ∈ extension.support) :
    Real.log ((extension assignment).toReal) =
      Real.log ((source (projectObs assignment)).toReal) +
        hRelative.potential.eval assignment := by
  have hSupport := (hRelative.mem_support_iff assignment).1 hAssignment
  have hSourcePos : 0 < (source (projectObs assignment)).toReal :=
    ENNReal.toReal_pos
      ((PMF.mem_support_iff source _).1 hSupport.1)
      (source.apply_ne_top _)
  rw [hRelative.probability_eq, relativeGibbsFactor,
    if_pos hSupport.2, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul hSourcePos.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- The absorbed-normalizer representation gives the manuscript's displayed
formula with the explicit positive normalizer `Z = 1`. -/
theorem RelativeFaceGibbsCertificate.exists_normalizer
    {Source : Type u} {Fresh : Type v}
    [Fintype Source] [Fintype Fresh]
    [DecidableEq Source] [DecidableEq Fresh]
    {k : Nat}
    {source : Distribution (Assignment Source)}
    {extension : Distribution (Assignment (Sum Source Fresh))}
    (hRelative : RelativeFaceGibbsCertificate k source extension) :
    ∃ Z : ENNReal, Z ≠ 0 ∧ Z ≠ ⊤ ∧ ∀ assignment,
      extension assignment =
        source (projectObs assignment) *
          relativeGibbsFactor hRelative.energy hRelative.potential assignment *
            Z⁻¹ := by
  refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
  intro assignment
  simpa using hRelative.probability_eq assignment

end KLocality
