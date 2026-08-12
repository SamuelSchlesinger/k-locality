import KLocality.FaceGibbsCharacterization
import KLocality.SelectorTrade

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Boundary-safe marginal trade certificates

A marginal trade certificate is a polynomial identity in visible cell
probabilities.  After every visible cell is expanded as a sum over its latent
fiber, the positive and negative joint monomials have the same multiset of
order-`k` feature profiles.  The face--Gibbs theorem makes joint monomials with
the same profile equal even on the boundary of the probability simplex.

This gives an exact, finite, weight-sensitive obstruction to a localization
with a prescribed latent type.
-/

/-- The total order-`k` Boolean-feature profile of an ordered tuple of cube
points.  Rational values make concrete profile equalities decidable by kernel
reduction. -/
def tupleFeatureProfile
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k degree : Nat) (tuple : Fin degree → Assignment Var) :
    FeatureScope Var k → ℚ :=
  fun scope => ∑ index : Fin degree,
    rationalMonomialValue scope.1 (tuple index)

/-- Equality of tuple profiles is exactly equality of every order-at-most-`k`
feature count. -/
def TupleFeatureBalanced
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) {degree : Nat}
    (left right : Fin degree → Assignment Var) : Prop :=
  tupleFeatureProfile k degree left = tupleFeatureProfile k degree right

theorem sum_featurePolynomial_eval_eq_of_tupleFeatureBalanced
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k degree : Nat}
    {left right : Fin degree → Assignment Var}
    (hBalanced : TupleFeatureBalanced k left right)
    (polynomial : FeaturePolynomial Var k) :
    (∑ index : Fin degree, polynomial.eval (left index)) =
      ∑ index : Fin degree, polynomial.eval (right index) := by
  classical
  unfold FeaturePolynomial.eval
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro scope _
  have hProfile := congrFun hBalanced scope
  have hCast := congrArg (fun value : ℚ => (value : ℝ)) hProfile
  have hMonomial :
      (∑ index : Fin degree, monomialValue scope.1 (left index)) =
        ∑ index : Fin degree, monomialValue scope.1 (right index) := by
    simpa [tupleFeatureProfile, Rat.cast_sum] using hCast
  rw [← Finset.mul_sum, ← Finset.mul_sum, hMonomial]

/-- The exposed support part of face--Gibbs makes membership of two balanced
tuples equivalent coordinatewise: one tuple lies wholly on the face iff the
other does. -/
theorem all_mem_support_iff_of_tupleFeatureBalanced
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k degree : Nat} {p : Distribution (Assignment Var)}
    (hFacial : IsFacialSupport k p.support)
    {left right : Fin degree → Assignment Var}
    (hBalanced : TupleFeatureBalanced k left right) :
    (∀ index, left index ∈ p.support) ↔
      ∀ index, right index ∈ p.support := by
  classical
  rcases hFacial with ⟨energy, hNonnegative, hZeroSet⟩
  have hEnergySum :=
    sum_featurePolynomial_eval_eq_of_tupleFeatureBalanced hBalanced energy
  have hAll_iff_sum_zero : ∀ tuple : Fin degree → Assignment Var,
      (∀ index, tuple index ∈ p.support) ↔
        (∑ index : Fin degree, energy.eval (tuple index)) = 0 := by
    intro tuple
    constructor
    · intro hAll
      apply Finset.sum_eq_zero
      intro index _
      exact (hZeroSet (tuple index)).2 (hAll index)
    · intro hSum index
      apply (hZeroSet (tuple index)).1
      have hLe : energy.eval (tuple index) ≤
          ∑ candidate : Fin degree, energy.eval (tuple candidate) := by
        exact Finset.single_le_sum
          (fun candidate _ => hNonnegative (tuple candidate))
          (Finset.mem_univ index)
      rw [hSum] at hLe
      exact le_antisymm hLe (hNonnegative (tuple index))
  rw [hAll_iff_sum_zero left, hAll_iff_sum_zero right, hEnergySum]

/-- Boundary-safe toric identity.  Any two ordered tuples with the same
order-`k` feature profile have equal products of probabilities under a
face--Gibbs law.  This includes zeros on proper exposed faces. -/
theorem prod_toReal_eq_of_tupleFeatureBalanced
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k degree : Nat} {p : Distribution (Assignment Var)}
    (hFaceGibbs : IsFaceGibbs k p)
    {left right : Fin degree → Assignment Var}
    (hBalanced : TupleFeatureBalanced k left right) :
    (∏ index : Fin degree, (p (left index)).toReal) =
      ∏ index : Fin degree, (p (right index)).toReal := by
  classical
  rcases hFaceGibbs with ⟨hFacial, theta, hLogDensity⟩
  have hSupportEquiv :=
    all_mem_support_iff_of_tupleFeatureBalanced hFacial hBalanced
  by_cases hLeftSupport : ∀ index, left index ∈ p.support
  · have hRightSupport : ∀ index, right index ∈ p.support :=
      hSupportEquiv.mp hLeftSupport
    have hLeftFormula : ∀ index,
        (p (left index)).toReal = Real.exp (theta.eval (left index)) := by
      intro index
      have hPositive : 0 < (p (left index)).toReal :=
        ENNReal.toReal_pos
          ((PMF.mem_support_iff p (left index)).1 (hLeftSupport index))
          (p.apply_ne_top (left index))
      calc
        (p (left index)).toReal =
            Real.exp (Real.log (p (left index)).toReal) :=
          (Real.exp_log hPositive).symm
        _ = Real.exp (theta.eval (left index)) := by
          rw [hLogDensity (left index) (hLeftSupport index)]
    have hRightFormula : ∀ index,
        (p (right index)).toReal = Real.exp (theta.eval (right index)) := by
      intro index
      have hPositive : 0 < (p (right index)).toReal :=
        ENNReal.toReal_pos
          ((PMF.mem_support_iff p (right index)).1 (hRightSupport index))
          (p.apply_ne_top (right index))
      calc
        (p (right index)).toReal =
            Real.exp (Real.log (p (right index)).toReal) :=
          (Real.exp_log hPositive).symm
        _ = Real.exp (theta.eval (right index)) := by
          rw [hLogDensity (right index) (hRightSupport index)]
    simp_rw [hLeftFormula, hRightFormula, ← Real.exp_sum]
    rw [sum_featurePolynomial_eval_eq_of_tupleFeatureBalanced hBalanced theta]
  · have hRightSupport : ¬∀ index, right index ∈ p.support := by
      intro hRight
      exact hLeftSupport (hSupportEquiv.mpr hRight)
    push_neg at hLeftSupport hRightSupport
    rcases hLeftSupport with ⟨leftIndex, hLeftOutside⟩
    rcases hRightSupport with ⟨rightIndex, hRightOutside⟩
    have hLeftZero : (p (left leftIndex)).toReal = 0 := by
      rw [(p.apply_eq_zero_iff (left leftIndex)).2 hLeftOutside,
        ENNReal.toReal_zero]
    have hRightZero : (p (right rightIndex)).toReal = 0 := by
      rw [(p.apply_eq_zero_iff (right rightIndex)).2 hRightOutside,
        ENNReal.toReal_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ leftIndex) hLeftZero,
      Finset.prod_eq_zero (Finset.mem_univ rightIndex) hRightZero]

/-- Split a joint assignment into its visible and latent restrictions. -/
def jointAssignmentEquiv
    (ObsVar : Type u) (LatVar : Type v) :
    Assignment (Sum ObsVar LatVar) ≃
      Assignment ObsVar × Assignment LatVar :=
  Equiv.sumArrowEquivProdArrow ObsVar LatVar Bool

@[simp]
theorem jointAssignmentEquiv_symm_apply
    {ObsVar : Type u} {LatVar : Type v}
    (visible : Assignment ObsVar) (latent : Assignment LatVar) :
    (jointAssignmentEquiv ObsVar LatVar).symm (visible, latent) =
      jointAssignment visible latent :=
  rfl

/-- A visible marginal cell is the finite sum of the real joint weights in
its latent fiber. -/
theorem map_projectObs_apply_toReal
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (p : Distribution (Assignment (Sum ObsVar LatVar)))
    (visible : Assignment ObsVar) :
    ((p.map projectObs) visible).toReal =
      ∑ latent : Assignment LatVar,
        (p (jointAssignment visible latent)).toReal := by
  classical
  rw [PMF.map_apply]
  simp only [tsum_fintype]
  rw [ENNReal.toReal_sum]
  · rw [← (jointAssignmentEquiv ObsVar LatVar).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single visible]
    · simp
    · intro other hOther
      have hVisibleOther : visible ≠ other := Ne.symm hOther
      simp [hVisibleOther]
  · intro joint _
    split <;> simp [p.apply_ne_top]

/-- Expand a product of visible marginal cells into all choices of one latent
witness per factor. -/
theorem prod_map_projectObs_apply_toReal
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (p : Distribution (Assignment (Sum ObsVar LatVar)))
    {degree : Nat} (visible : Fin degree → Assignment ObsVar) :
    (∏ index : Fin degree, ((p.map projectObs) (visible index)).toReal) =
      ∑ latent : Fin degree → Assignment LatVar,
        ∏ index : Fin degree,
          (p (jointAssignment (visible index) (latent index))).toReal := by
  classical
  simp_rw [map_projectObs_apply_toReal p]
  exact Fintype.prod_sum _

/-- Lift a visible tuple and one latent choice per factor to a tuple of joint
assignments. -/
def liftTuple
    {ObsVar : Type u} {LatVar : Type v} {degree : Nat}
    (visible : Fin degree → Assignment ObsVar)
    (latent : Fin degree → Assignment LatVar) :
    Fin degree → Assignment (Sum ObsVar LatVar) :=
  fun index => jointAssignment (visible index) (latent index)

/-- A finite exact certificate for a polynomial identity obeyed by every
order-`k` localization with latent type `LatVar`.  Each side is a sum of
`termCount` monomials of homogeneous degree `degree`. -/
structure MarginalTradeCertificate
    (k degree termCount : Nat)
    (ObsVar : Type u) (LatVar : Type v)
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar] where
  positive : Fin termCount → Fin degree → Assignment ObsVar
  negative : Fin termCount → Fin degree → Assignment ObsVar
  profileBalance :
    ((Finset.univ : Finset
        (Fin termCount × (Fin degree → Assignment LatVar))).val.map
      (fun expanded => tupleFeatureProfile k degree
        (liftTuple (positive expanded.1) expanded.2))) =
    ((Finset.univ : Finset
        (Fin termCount × (Fin degree → Assignment LatVar))).val.map
      (fun expanded => tupleFeatureProfile k degree
        (liftTuple (negative expanded.1) expanded.2)))

namespace MarginalTradeCertificate

/-- Sum of the positive visible monomials evaluated on a real table. -/
def positiveValue
    {k degree termCount : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (certificate : MarginalTradeCertificate k degree termCount ObsVar LatVar)
    (weights : Assignment ObsVar → ℝ) : ℝ :=
  ∑ term : Fin termCount,
    ∏ index : Fin degree, weights (certificate.positive term index)

/-- Sum of the negative visible monomials evaluated on a real table. -/
def negativeValue
    {k degree termCount : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (certificate : MarginalTradeCertificate k degree termCount ObsVar LatVar)
    (weights : Assignment ObsVar → ℝ) : ℝ :=
  ∑ term : Fin termCount,
    ∏ index : Fin degree, weights (certificate.negative term index)

/-- Choose a joint monomial realizing a feature profile, when one exists.
The boundary-safe toric identity makes its value independent of this choice. -/
noncomputable def productAtProfile
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k degree : Nat) (p : Distribution (Assignment Var))
    (profile : FeatureScope Var k → ℚ) : ℝ := by
  classical
  exact if hExists : ∃ tuple : Fin degree → Assignment Var,
      tupleFeatureProfile k degree tuple = profile then
    ∏ index : Fin degree, (p (hExists.choose index)).toReal
  else 0

theorem prod_toReal_eq_productAtProfile
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k degree : Nat} {p : Distribution (Assignment Var)}
    (hFaceGibbs : IsFaceGibbs k p)
    (tuple : Fin degree → Assignment Var) :
    (∏ index : Fin degree, (p (tuple index)).toReal) =
      productAtProfile k degree p (tupleFeatureProfile k degree tuple) := by
  classical
  unfold productAtProfile
  split_ifs with hExists
  · exact prod_toReal_eq_of_tupleFeatureBalanced hFaceGibbs
      hExists.choose_spec.symm
  · exact False.elim (hExists ⟨tuple, rfl⟩)

/-- The certificate identity holds for every marginal of a face--Gibbs joint
law, including laws supported on a proper exposed face. -/
theorem value_eq_of_faceGibbs_marginal
    {k degree termCount : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (certificate : MarginalTradeCertificate k degree termCount ObsVar LatVar)
    (joint : Distribution (Assignment (Sum ObsVar LatVar)))
    (hFaceGibbs : IsFaceGibbs k joint) :
    certificate.positiveValue
        (fun visible => ((joint.map projectObs) visible).toReal) =
      certificate.negativeValue
        (fun visible => ((joint.map projectObs) visible).toReal) := by
  classical
  unfold positiveValue negativeValue
  simp_rw [prod_map_projectObs_apply_toReal joint]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  simp_rw [prod_toReal_eq_productAtProfile hFaceGibbs]
  have hProfileSums := congrArg
    (fun profiles : Multiset
        (FeatureScope (Sum ObsVar LatVar) k → ℚ) =>
      (profiles.map (productAtProfile k degree joint)).sum)
    certificate.profileBalance
  simpa [liftTuple] using hProfileSums

/-- Every `k`-localization with the certificate's latent type obeys its
visible polynomial identity. -/
theorem value_eq_of_localization
    {k degree termCount : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (certificate : MarginalTradeCertificate k degree termCount ObsVar LatVar)
    {visible : Distribution (Assignment ObsVar)}
    (localization : KLocalization k ObsVar LatVar visible) :
    certificate.positiveValue (fun x => (visible x).toReal) =
      certificate.negativeValue (fun x => (visible x).toReal) := by
  have hFaceGibbs : IsFaceGibbs k localization.lifted :=
    (isKLocalMarginal_iff_isFaceGibbs k localization.lifted).1
      localization.kLocal
  have hIdentity := certificate.value_eq_of_faceGibbs_marginal
    localization.lifted hFaceGibbs
  rw [localization.marginal] at hIdentity
  exact hIdentity

/-- A detected nonzero trade rules out a localization with the prescribed
latent type. -/
theorem obstructs_localization
    {k degree termCount : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (certificate : MarginalTradeCertificate k degree termCount ObsVar LatVar)
    {visible : Distribution (Assignment ObsVar)}
    (hDetects : certificate.positiveValue (fun x => (visible x).toReal) ≠
      certificate.negativeValue (fun x => (visible x).toReal)) :
    ¬Nonempty (KLocalization k ObsVar LatVar visible) := by
  rintro ⟨localization⟩
  exact hDetects (certificate.value_eq_of_localization localization)

/-- A family of detected marginal trades for every latent-bit count through
`budget` gives the literal complexity lower bound `budget < LC_k(D)`.  The
certificate degree and number of terms may vary with the latent count. -/
theorem localizationComplexity_gt_of_tradeCertificates
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {k budget : Nat} (hk : 2 ≤ k)
    (visible : Distribution (Assignment ObsVar))
    (certificates : ∀ latentBits, latentBits ≤ budget →
      ∃ degree termCount,
        ∃ certificate : MarginalTradeCertificate
            k degree termCount ObsVar (Fin latentBits),
          certificate.positiveValue (fun x => (visible x).toReal) ≠
            certificate.negativeValue (fun x => (visible x).toReal)) :
    budget < localizationComplexity k ObsVar visible := by
  have hExists := kLocalization_exists visible hk
  have hOptimal := localizationComplexity_spec k ObsVar visible hExists
  by_contra hNot
  have hAtMost : localizationComplexity k ObsVar visible ≤ budget :=
    Nat.le_of_not_gt hNot
  rcases certificates (localizationComplexity k ObsVar visible) hAtMost with
    ⟨degree, termCount, certificate, hDetects⟩
  exact certificate.obstructs_localization hDetects hOptimal

end MarginalTradeCertificate

end KLocality
