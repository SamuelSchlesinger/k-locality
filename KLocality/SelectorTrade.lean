import KLocality.SelectorLeakage

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Rational selector trade certificates

The dual obstruction in Proposition `prop:selector-lp` is a signed rational
table in the kernel of the order-`k` moment map.  Its coefficients may be
arbitrary on the selected graph, must be nonnegative off the graph, and have
positive total coefficient above the visible complement.  This file turns
that finite rational certificate into an honest leaking PMF.
-/

/-- Boolean monomial values over the rationals. -/
def rationalMonomialValue
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (scope : Finset Var) (assignment : Assignment Var) : ℚ :=
  if scope ⊆ trueCoordinates assignment then 1 else 0

@[simp]
theorem cast_rationalMonomialValue
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (scope : Finset Var) (assignment : Assignment Var) :
    (rationalMonomialValue scope assignment : ℝ) =
      monomialValue scope assignment := by
  by_cases h : scope ⊆ trueCoordinates assignment <;>
    simp [rationalMonomialValue, monomialValue, h]

/-- Rational Farkas certificate `(D_σ)` for one selector.  `coefficient`
combines the unrestricted graph multipliers `λ` and the nonnegative off-graph
multipliers `μ`; the last field uses the manuscript's normalization
`∑_{B} μ = 1`. -/
structure RationalSelectorDualCertificate
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) {visibleSupport : Finset (Assignment ObsVar)}
    (hVisible : visibleSupport.Nonempty)
    (selector : Selector visibleSupport LatVar) where
  coefficient : Assignment (Sum ObsVar LatVar) → ℚ
  momentBalance : ∀ scope : FeatureScope (Sum ObsVar LatVar) k,
    ∑ joint : Assignment (Sum ObsVar LatVar),
      coefficient joint * rationalMonomialValue scope.1 joint = 0
  nonnegativeOffGraph : ∀ joint,
    joint ∉ (selectorGraphDistribution hVisible selector).support →
      0 ≤ coefficient joint
  outsideTotal :
    ∑ joint ∈ (Finset.univ.filter fun joint : Assignment (Sum ObsVar LatVar) =>
        projectObs joint ∉ visibleSupport), coefficient joint = 1

namespace RationalSelectorDualCertificate

/-- Regard the rational dual table as a real tangent vector. -/
def realDirection
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {visibleSupport : Finset (Assignment ObsVar)}
    {hVisible : visibleSupport.Nonempty}
    {selector : Selector visibleSupport LatVar}
    (certificate : RationalSelectorDualCertificate k hVisible selector) :
    Assignment (Sum ObsVar LatVar) → ℝ :=
  fun joint => certificate.coefficient joint

theorem realDirection_mem_momentMap_ker
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {visibleSupport : Finset (Assignment ObsVar)}
    {hVisible : visibleSupport.Nonempty}
    {selector : Selector visibleSupport LatVar}
    (certificate : RationalSelectorDualCertificate k hVisible selector) :
    certificate.realDirection ∈
      LinearMap.ker (FeaturePolynomial.momentMap k) := by
  rw [LinearMap.mem_ker]
  funext scope
  rw [FeaturePolynomial.momentMap_apply]
  have hBalance := congrArg (fun value : ℚ => (value : ℝ))
    (certificate.momentBalance scope)
  simpa [realDirection, Rat.cast_sum] using hBalance

theorem realDirection_nonnegative_outside_graph
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {visibleSupport : Finset (Assignment ObsVar)}
    {hVisible : visibleSupport.Nonempty}
    {selector : Selector visibleSupport LatVar}
    (certificate : RationalSelectorDualCertificate k hVisible selector) :
    ∀ joint : OutsideSupport (selectorGraphDistribution hVisible selector),
      0 ≤ certificate.realDirection joint.1 := by
  intro joint
  exact Rat.cast_nonneg.mpr
    (certificate.nonnegativeOffGraph joint.1 joint.2)

/-- The normalized positive mass above the visible complement contains a
strictly positive rational coordinate. -/
theorem exists_positive_outside
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {visibleSupport : Finset (Assignment ObsVar)}
    {hVisible : visibleSupport.Nonempty}
    {selector : Selector visibleSupport LatVar}
    (certificate : RationalSelectorDualCertificate k hVisible selector) :
    ∃ joint : Assignment (Sum ObsVar LatVar),
      projectObs joint ∉ visibleSupport ∧
        0 < certificate.coefficient joint := by
  classical
  let outside : Finset (Assignment (Sum ObsVar LatVar)) :=
    Finset.univ.filter fun joint => projectObs joint ∉ visibleSupport
  by_contra hNone
  push_neg at hNone
  have hNonpos : ∀ joint ∈ outside, certificate.coefficient joint ≤ 0 := by
    intro joint hJoint
    exact hNone joint (by simpa [outside] using hJoint)
  have hSumNonpos :
      (∑ joint ∈ outside, certificate.coefficient joint) ≤ 0 :=
    Finset.sum_nonpos hNonpos
  have hSumOne :
      (∑ joint ∈ outside, certificate.coefficient joint) = 1 := by
    simpa [outside] using certificate.outsideTotal
  rw [hSumOne] at hSumNonpos
  norm_num at hSumNonpos

/-- Compile an exact rational dual certificate into an actual law with the
same order-`k` moments that leaks above the visible complement. -/
theorem selectorLeaks
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {visibleSupport : Finset (Assignment ObsVar)}
    {hVisible : visibleSupport.Nonempty}
    {selector : Selector visibleSupport LatVar}
    (certificate : RationalSelectorDualCertificate k hVisible selector) :
    KLocality.SelectorLeaks k hVisible selector := by
  classical
  rcases certificate.exists_positive_outside with
    ⟨leakPoint, hLeakOutside, hLeakPositive⟩
  let graphLaw := selectorGraphDistribution hVisible selector
  have hLeakOffGraph : leakPoint ∉ graphLaw.support :=
    not_mem_selectorGraphDistribution_support_of_projectObs_not_mem
      hVisible selector hLeakOutside
  rcases exists_sameMoments_distribution_of_kernel_direction
      graphLaw certificate.realDirection
      certificate.realDirection_mem_momentMap_ker
      certificate.realDirection_nonnegative_outside_graph with
    ⟨epsilon, leakingLaw, hEpsilon, hMoments, hOutsideWeights⟩
  have hLeakWeight :
      (leakingLaw leakPoint).toReal =
        epsilon * certificate.realDirection leakPoint :=
    hOutsideWeights ⟨leakPoint, hLeakOffGraph⟩
  have hLeakWeightPositive : 0 < (leakingLaw leakPoint).toReal := by
    rw [hLeakWeight]
    exact mul_pos hEpsilon (Rat.cast_pos.mpr hLeakPositive)
  have hLeakSupport : leakPoint ∈ leakingLaw.support := by
    apply (PMF.mem_support_iff leakingLaw leakPoint).2
    intro hZero
    rw [hZero, ENNReal.toReal_zero] at hLeakWeightPositive
    exact (lt_irrefl 0) hLeakWeightPositive
  exact ⟨leakingLaw, hMoments, leakPoint, hLeakSupport, hLeakOutside⟩

/-- The compiled leaking law agrees on the complete collection of
order-at-most-`k` marginals, not merely on a chosen moment basis. -/
theorem exists_leakingLaw_sameMarginals
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {k : Nat} {visibleSupport : Finset (Assignment ObsVar)}
    {hVisible : visibleSupport.Nonempty}
    {selector : Selector visibleSupport LatVar}
    (certificate : RationalSelectorDualCertificate k hVisible selector) :
    ∃ leakingLaw : Distribution (Assignment (Sum ObsVar LatVar)),
      SameMarginalsUpTo k
        (selectorGraphDistribution hVisible selector) leakingLaw ∧
        ∃ joint ∈ leakingLaw.support,
          projectObs joint ∉ visibleSupport := by
  rcases certificate.selectorLeaks with
    ⟨leakingLaw, hMoments, joint, hJoint, hOutside⟩
  exact ⟨leakingLaw,
    (sameFeatureMomentsUpTo_iff_sameMarginalsUpTo k _ _).1 hMoments,
    joint, hJoint, hOutside⟩

end RationalSelectorDualCertificate

/-- A rational dual certificate for every selector rules out a localization
with the indicated latent type.  This is the checkable lower-bound interface
of Proposition `prop:selector-lp`. -/
theorem rationalSelectorDualCertificates_obstruct_localization
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (k : Nat) (visibleSupport : Finset (Assignment ObsVar))
    (hVisible : visibleSupport.Nonempty)
    (p : Distribution (Assignment ObsVar))
    (hpSupport : p.support = (visibleSupport : Set (Assignment ObsVar)))
    (certificates : ∀ selector : Selector visibleSupport LatVar,
      RationalSelectorDualCertificate k hVisible selector) :
    ¬Nonempty (KLocalization k ObsVar LatVar p) := by
  apply everySelectorLeaks_obstructs_localization
    k visibleSupport hVisible p hpSupport
  intro selector
  exact (certificates selector).selectorLeaks

end KLocality
