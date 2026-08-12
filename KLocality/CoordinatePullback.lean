import KLocality.CoordinateSubstitution

namespace KLocality

open scoped BigOperators

universe u v w

/-!
# Pulling distributions back through duplication/fixing parametrizations

A `CoordinateParametrization` identifies a Boolean cube with an event in a
larger cube, and records that the identification is induced by duplicating
variables and fixing variables to constants.  Probability laws supported in
that event can be pulled back without changing weights; the substitution
theorems then preserve face--Gibbs locality.
-/

/-- A bijective parametrization of an event by a Boolean cube, induced by a
coordinate duplication/fixing recipe. -/
structure CoordinateParametrization
    (Source : Type u) (Target : Type v)
    (event : Set (Assignment Source)) where
  recipe : Source → CoordinateRecipe Target
  equiv : Assignment Target ≃ event
  equiv_apply : ∀ assignment,
    (equiv assignment).1 = substituteAssignment recipe assignment

/-- Pull a PMF supported in `event` back through its coordinate
parametrization. -/
noncomputable def pullbackDistribution
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    {event : Set (Assignment Source)}
    (p : Distribution (Assignment Source))
    (hSupport : p.support ⊆ event)
    (parametrization : CoordinateParametrization Source Target event) :
    Distribution (Assignment Target) := by
  classical
  refine PMF.ofFintype
    (fun assignment => p (parametrization.equiv assignment).1) ?_
  have hFunctionSupport : Function.support (fun x => p x) ⊆ event := by
    intro x hx
    exact hSupport ((PMF.mem_support_iff p x).2 hx)
  have hSubtypeTsum :
      (∑' x : event, p x.1) = 1 := by
    rw [tsum_subtype_eq_of_support_subset hFunctionSupport, p.tsum_coe]
  calc
    ∑ assignment : Assignment Target,
        p (parametrization.equiv assignment).1 =
        ∑ x : event, p x.1 := by
      simpa using parametrization.equiv.sum_comp (fun x : event => p x.1)
    _ = 1 := by simpa only [tsum_fintype] using hSubtypeTsum

@[simp]
theorem pullbackDistribution_apply
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    {event : Set (Assignment Source)}
    (p : Distribution (Assignment Source))
    (hSupport : p.support ⊆ event)
    (parametrization : CoordinateParametrization Source Target event)
    (assignment : Assignment Target) :
    pullbackDistribution p hSupport parametrization assignment =
      p (parametrization.equiv assignment).1 :=
  rfl

theorem mem_support_pullbackDistribution_iff
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    {event : Set (Assignment Source)}
    (p : Distribution (Assignment Source))
    (hSupport : p.support ⊆ event)
    (parametrization : CoordinateParametrization Source Target event)
    (assignment : Assignment Target) :
    assignment ∈ (pullbackDistribution p hSupport parametrization).support ↔
      (parametrization.equiv assignment).1 ∈ p.support := by
  rw [PMF.mem_support_iff, PMF.mem_support_iff]
  rfl

/-- Pulling back a face--Gibbs law through duplication/fixing preserves its
face--Gibbs certificate. -/
theorem isFaceGibbs_pullbackDistribution
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    {event : Set (Assignment Source)} {k : Nat}
    (p : Distribution (Assignment Source))
    (hSupport : p.support ⊆ event)
    (parametrization : CoordinateParametrization Source Target event)
    (hFaceGibbs : IsFaceGibbs k p) :
    IsFaceGibbs k (pullbackDistribution p hSupport parametrization) := by
  classical
  rcases hFaceGibbs with ⟨⟨energy, hNonneg, hZero⟩, theta, hLog⟩
  let pulledEnergy := energy.substitute parametrization.recipe
  let pulledTheta := theta.substitute parametrization.recipe
  refine ⟨⟨pulledEnergy, ?_, ?_⟩, pulledTheta, ?_⟩
  · intro assignment
    rw [show pulledEnergy.eval assignment =
        energy.eval (substituteAssignment parametrization.recipe assignment) by
      exact FeaturePolynomial.eval_substitute _ _ _]
    exact hNonneg _
  · intro assignment
    rw [show pulledEnergy.eval assignment =
        energy.eval (substituteAssignment parametrization.recipe assignment) by
      exact FeaturePolynomial.eval_substitute _ _ _]
    rw [← parametrization.equiv_apply assignment, hZero,
      mem_support_pullbackDistribution_iff]
  · intro assignment hAssignment
    have hSourceSupport :
        (parametrization.equiv assignment).1 ∈ p.support :=
      (mem_support_pullbackDistribution_iff p hSupport parametrization assignment).1
        hAssignment
    rw [pullbackDistribution_apply, hLog _ hSourceSupport]
    change theta.eval (parametrization.equiv assignment).1 =
      pulledTheta.eval assignment
    rw [parametrization.equiv_apply]
    symm
    exact FeaturePolynomial.eval_substitute _ _ _

/-- Locality is preserved by a bijective duplication/fixing pullback. -/
theorem isKLocalMarginal_pullbackDistribution
    {Source : Type u} {Target : Type v}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    {event : Set (Assignment Source)} {k : Nat}
    (p : Distribution (Assignment Source))
    (hSupport : p.support ⊆ event)
    (parametrization : CoordinateParametrization Source Target event)
    (hLocal : IsKLocalMarginal k p) :
    IsKLocalMarginal k (pullbackDistribution p hSupport parametrization) :=
  isKLocalMarginal_of_isFaceGibbs k _
    (isFaceGibbs_pullbackDistribution p hSupport parametrization
      ((isKLocalMarginal_iff_isFaceGibbs k p).1 hLocal))

/-- Naturality of pullback distributions in a commuting square. -/
theorem map_pullbackDistribution
    {Source : Type u} {Target : Type v}
    {Source' : Type w} {Target' : Type*}
    [Fintype Source] [Fintype Target]
    [Fintype Source'] [Fintype Target']
    {event : Set (Assignment Source)}
    {event' : Set (Assignment Source')}
    (p : Distribution (Assignment Source))
    (p' : Distribution (Assignment Source'))
    (hSupport : p.support ⊆ event)
    (hSupport' : p'.support ⊆ event')
    (parametrization : CoordinateParametrization Source Target event)
    (parametrization' : CoordinateParametrization Source' Target' event')
    (sourceMap : Assignment Source → Assignment Source')
    (targetMap : Assignment Target → Assignment Target')
    (hMap : p.map sourceMap = p')
    (hCommute : ∀ assignment,
      sourceMap (parametrization.equiv assignment).1 =
        (parametrization'.equiv (targetMap assignment)).1) :
    (pullbackDistribution p hSupport parametrization).map targetMap =
      pullbackDistribution p' hSupport' parametrization' := by
  classical
  apply PMF.ext
  intro target
  rw [PMF.map_apply, pullbackDistribution_apply]
  simp only [tsum_fintype, pullbackDistribution_apply]
  have hAtTarget : p' (parametrization'.equiv target).1 =
      ∑ source : Assignment Source,
        if (parametrization'.equiv target).1 = sourceMap source then p source else 0 := by
    rw [← hMap, PMF.map_apply]
    simp only [tsum_fintype]
    apply Finset.sum_congr rfl
    intro source _
    by_cases hEq : (parametrization'.equiv target).1 = sourceMap source <;>
      simp [hEq]
  rw [hAtTarget]
  let summand : Assignment Source → ENNReal := fun source =>
    if (parametrization'.equiv target).1 = sourceMap source then p source else 0
  have hSummandSupport : Function.support summand ⊆ event := by
    intro source hSource
    by_cases hEq : (parametrization'.equiv target).1 = sourceMap source
    · have hpNe : p source ≠ 0 := by simpa [summand, hEq] using hSource
      exact hSupport ((PMF.mem_support_iff p source).2 hpNe)
    · simp [summand, hEq] at hSource
  have hRestrict :
      (∑ source : Assignment Source, summand source) =
        ∑ source : event, summand source.1 := by
    have hTsum := tsum_subtype_eq_of_support_subset hSummandSupport
    simpa only [tsum_fintype] using hTsum.symm
  rw [show (∑ source : Assignment Source,
      if (parametrization'.equiv target).1 = sourceMap source then p source else 0) =
      ∑ source : Assignment Source, summand source by rfl,
    hRestrict, ← parametrization.equiv.sum_comp]
  apply Finset.sum_congr rfl
  intro assignment _
  unfold summand
  rw [hCommute assignment]
  simp only [Subtype.val_inj, parametrization'.equiv.apply_eq_iff_eq]

end KLocality
