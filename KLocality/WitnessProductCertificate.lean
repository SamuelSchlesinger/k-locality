import KLocality.GroundStateExtension
import KLocality.SelectorTrade

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Sign-definite witness-product certificates

This is a reusable finite obstruction to `k`-localization with a fixed hidden
type.  A certificate gives a rational direction on the visible cube which
annihilates every product of one order-`k` feature monomial per hidden
assignment.  Off the requested visible support the direction is nonnegative,
and it is positive somewhere.

For a hypothetical localization, multiply every hidden slice of a
nonnegative polynomial exposing the lifted support.  Expanding the product
reduces its alternating sum to the certificate identities.  On the other
hand, the product vanishes on the visible support and is positive off it, so
the same sign-definite sum is strictly positive.
-/

/-- A rational, finite certificate ruling out an order-`k` localization with
hidden variable type `LatVar`. -/
structure WitnessProductCertificate
    (k : Nat) (ObsVar : Type u) (LatVar : Type v)
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (visibleSupport : Set (Assignment ObsVar)) where
  direction : Assignment ObsVar → ℚ
  monomialBalance :
    ∀ scopes : Assignment LatVar → FeatureScope (Sum ObsVar LatVar) k,
      (∑ visible : Assignment ObsVar,
        direction visible *
          ∏ latent : Assignment LatVar,
            rationalMonomialValue (scopes latent).1
              (jointAssignment visible latent)) = 0
  nonnegativeOutside :
    ∀ visible, visible ∉ visibleSupport → 0 ≤ direction visible
  positiveOutside :
    ∃ visible, visible ∉ visibleSupport ∧ 0 < direction visible

namespace WitnessProductCertificate

/-- Real embedding of a certificate direction. -/
noncomputable def realDirection
    {k : Nat} {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {visibleSupport : Set (Assignment ObsVar)}
    (certificate : WitnessProductCertificate k ObsVar LatVar visibleSupport)
    (visible : Assignment ObsVar) : ℝ :=
  certificate.direction visible

/-- Product of all hidden slices of an exposing feature polynomial. -/
noncomputable def witnessProduct
    {k : Nat} {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (energy : FeaturePolynomial (Sum ObsVar LatVar) k)
    (visible : Assignment ObsVar) : ℝ :=
  ∏ latent : Assignment LatVar,
    energy.eval (jointAssignment visible latent)

/-- Compile the rational monomial balances into annihilation of the product
of arbitrary real feature polynomials. -/
theorem sum_realDirection_mul_witnessProduct_eq_zero
    {k : Nat} {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {visibleSupport : Set (Assignment ObsVar)}
    (certificate : WitnessProductCertificate k ObsVar LatVar visibleSupport)
    (energy : FeaturePolynomial (Sum ObsVar LatVar) k) :
    (∑ visible : Assignment ObsVar,
      certificate.realDirection visible * witnessProduct energy visible) = 0 := by
  classical
  have hRealBalance : ∀ scopes : Assignment LatVar →
      FeatureScope (Sum ObsVar LatVar) k,
      (∑ visible : Assignment ObsVar,
        certificate.realDirection visible *
          ∏ latent : Assignment LatVar,
            monomialValue (scopes latent).1
              (jointAssignment visible latent)) = 0 := by
    intro scopes
    have hCast := congrArg (fun value : ℚ => (value : ℝ))
      (certificate.monomialBalance scopes)
    simpa [realDirection, Rat.cast_sum] using hCast
  unfold witnessProduct FeaturePolynomial.eval
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scopes _
  simp_rw [Finset.prod_mul_distrib]
  calc
    (∑ visible : Assignment ObsVar,
        certificate.realDirection visible *
          ((∏ latent : Assignment LatVar, energy (scopes latent)) *
            ∏ latent : Assignment LatVar,
              monomialValue (scopes latent).1
                (jointAssignment visible latent))) =
        (∏ latent : Assignment LatVar, energy (scopes latent)) *
          ∑ visible : Assignment ObsVar,
            certificate.realDirection visible *
              ∏ latent : Assignment LatVar,
                monomialValue (scopes latent).1
                  (jointAssignment visible latent) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro visible _
      ring
    _ = 0 := by rw [hRealBalance scopes, mul_zero]

/-- The witness product vanishes precisely over the visible projection of
the exposed lifted support. -/
theorem witnessProduct_zero_iff
    {k : Nat} {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {groundStates : Set (Assignment (Sum ObsVar LatVar))}
    (energy : FeaturePolynomial (Sum ObsVar LatVar) k)
    (hZeroSet : ∀ joint, energy.eval joint = 0 ↔ joint ∈ groundStates)
    (visibleSupport : Set (Assignment ObsVar))
    (hProjection : projectObs '' groundStates = visibleSupport)
    (visible : Assignment ObsVar) :
    witnessProduct energy visible = 0 ↔ visible ∈ visibleSupport := by
  classical
  constructor
  · intro hProduct
    rw [witnessProduct, Finset.prod_eq_zero_iff] at hProduct
    rcases hProduct with ⟨latent, _hLatent, hZero⟩
    rw [hZeroSet] at hZero
    rw [← hProjection]
    exact ⟨jointAssignment visible latent, hZero, rfl⟩
  · intro hVisible
    rw [← hProjection] at hVisible
    rcases hVisible with ⟨joint, hJoint, hProject⟩
    rw [witnessProduct]
    apply Finset.prod_eq_zero (Finset.mem_univ (projectLat joint))
    have hDecompose :
        jointAssignment visible (projectLat joint) = joint := by
      rw [← hProject]
      exact jointAssignment_projectObs_projectLat joint
    rw [hDecompose]
    exact (hZeroSet joint).2 hJoint

theorem witnessProduct_pos_of_not_mem
    {k : Nat} {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {groundStates : Set (Assignment (Sum ObsVar LatVar))}
    (energy : FeaturePolynomial (Sum ObsVar LatVar) k)
    (hNonnegative : ∀ joint, 0 ≤ energy.eval joint)
    (hZeroSet : ∀ joint, energy.eval joint = 0 ↔ joint ∈ groundStates)
    (visibleSupport : Set (Assignment ObsVar))
    (hProjection : projectObs '' groundStates = visibleSupport)
    {visible : Assignment ObsVar} (hOutside : visible ∉ visibleSupport) :
    0 < witnessProduct energy visible := by
  classical
  rw [witnessProduct]
  apply Finset.prod_pos
  intro latent _
  have hJointOutside : jointAssignment visible latent ∉ groundStates := by
    intro hJoint
    apply hOutside
    rw [← hProjection]
    exact ⟨jointAssignment visible latent, hJoint, rfl⟩
  have hNonzero : energy.eval (jointAssignment visible latent) ≠ 0 := by
    exact fun hZero => hJointOutside ((hZeroSet _).1 hZero)
  exact lt_of_le_of_ne (hNonnegative _) (Ne.symm hNonzero)

/-- Soundness of a sign-definite witness-product certificate.  The theorem is
uniform in the visible distribution: only its support is used. -/
theorem obstructs_localization
    {k : Nat} {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    {visibleSupport : Set (Assignment ObsVar)}
    (certificate : WitnessProductCertificate k ObsVar LatVar visibleSupport)
    (visible : Distribution (Assignment ObsVar))
    (hSupport : visible.support = visibleSupport) :
    ¬Nonempty (KLocalization k ObsVar LatVar visible) := by
  rintro ⟨localization⟩
  let extension := localization.toGroundStateExtension
  rcases extension.facial with ⟨energy, hNonnegative, hZeroSet⟩
  have hProjection : projectObs '' extension.groundStates = visibleSupport := by
    calc
      projectObs '' extension.groundStates = visible.support :=
        extension.projection
      _ = visibleSupport := hSupport
  have hAnnihilates := certificate.sum_realDirection_mul_witnessProduct_eq_zero
    energy
  have hNonnegativeTerms :
      ∀ assignment ∈ (Finset.univ : Finset (Assignment ObsVar)),
        0 ≤ certificate.realDirection assignment *
          witnessProduct energy assignment := by
    intro assignment _
    by_cases hMember : assignment ∈ visibleSupport
    · have hZero := (witnessProduct_zero_iff energy hZeroSet
        visibleSupport hProjection assignment).2 hMember
      simp [hZero]
    · have hDirectionNonnegative :
          0 ≤ certificate.realDirection assignment :=
        Rat.cast_nonneg.mpr (certificate.nonnegativeOutside assignment hMember)
      have hProductPositive := witnessProduct_pos_of_not_mem energy
        hNonnegative hZeroSet visibleSupport hProjection hMember
      exact mul_nonneg hDirectionNonnegative hProductPositive.le
  rcases certificate.positiveOutside with
    ⟨positiveAssignment, hPositiveOutside, hDirectionPositiveRat⟩
  have hDirectionPositive :
      0 < certificate.realDirection positiveAssignment :=
    Rat.cast_pos.mpr hDirectionPositiveRat
  have hProductPositive := witnessProduct_pos_of_not_mem energy
    hNonnegative hZeroSet visibleSupport hProjection hPositiveOutside
  have hPositiveTerm :
      0 < certificate.realDirection positiveAssignment *
        witnessProduct energy positiveAssignment :=
    mul_pos hDirectionPositive hProductPositive
  have hPositiveSum :
      0 < ∑ assignment : Assignment ObsVar,
        certificate.realDirection assignment *
          witnessProduct energy assignment := by
    apply Finset.sum_pos' hNonnegativeTerms
    exact ⟨positiveAssignment, Finset.mem_univ _, hPositiveTerm⟩
  rw [hAnnihilates] at hPositiveSum
  exact (lt_irrefl 0) hPositiveSum

end WitnessProductCertificate

end KLocality
