import KLocality.GroundStateExtension
import KLocality.GroundStateProjection
import KLocality.QuadraticNAND
import KLocality.UniformParityLowerBound

namespace KLocality

open scoped BigOperators

/-!
# An explicit nontrivial lower bound for cubic localizations

The uniform distribution on even-parity seven-bit strings has cubic
localization complexity exactly two.  The lower bound is the finite
sign-definite witness-product argument: an `ell`-bit localization supplies a
product of `2^ell` nonnegative cubic face slices which vanishes exactly on the
visible support.  For `ell <= 1` this product has degree at most six, whereas
any nonnegative polynomial positive exactly on odd parity has degree seven.

Rather than introducing a polynomial degree API, the concrete degree-six
annihilation is recorded as an exact rational cube identity and replayed for
arbitrary real face coefficients.
-/

/-- Parity of a seven-bit assignment. -/
def paritySeven (assignment : BitVec 7) : Bool :=
  xor (xor (xor (assignment 0) (assignment 1))
      (xor (assignment 2) (assignment 3)))
    (xor (xor (assignment 4) (assignment 5)) (assignment 6))

/-- The explicit even-parity support. -/
def evenParitySeven : Finset (BitVec 7) :=
  Finset.univ.filter fun assignment => paritySeven assignment = false

theorem evenParitySeven_eq_evenParitySupport :
    evenParitySeven = evenParitySupport 7 := by
  decide +kernel

theorem evenParitySeven_nonempty : evenParitySeven.Nonempty := by
  decide +kernel

theorem evenParitySeven_card : evenParitySeven.card = 64 := by
  decide +kernel

/-- The explicit distribution used in the cubic lower bound. -/
noncomputable def evenParitySevenDistribution : Distribution (BitVec 7) :=
  uniformOn evenParitySeven evenParitySeven_nonempty

theorem evenParitySevenDistribution_eq_evenParityDistribution :
    evenParitySevenDistribution = evenParityDistribution 7 := by
  simp [evenParitySevenDistribution, evenParityDistribution,
    evenParitySeven_eq_evenParitySupport]

@[simp]
theorem evenParitySevenDistribution_support :
    evenParitySevenDistribution.support =
      (evenParitySeven : Set (BitVec 7)) := by
  simp [evenParitySevenDistribution]

/-- Alternating sign, chosen positive on odd parity. -/
def paritySevenDirectionRat (assignment : BitVec 7) : ℚ :=
  if paritySeven assignment then 1 else -1

theorem paritySevenDirectionRat_eq_evenParityDirectionRat :
    ∀ visible : BitVec 7,
      paritySevenDirectionRat visible = evenParityDirectionRat 7 visible := by
  decide +kernel

/-- Real embedding of the alternating direction. -/
noncomputable def paritySevenDirection (assignment : BitVec 7) : ℝ :=
  paritySevenDirectionRat assignment

/-- Product of all latent face slices above one visible assignment. -/
noncomputable def facialWitnessProduct
    {LatVar : Type*} [Fintype LatVar] [DecidableEq LatVar]
    (energy : FeaturePolynomial (Sum (Fin 7) LatVar) 3)
    (visible : BitVec 7) : ℝ :=
  ∏ latent : Assignment LatVar,
    energy.eval (jointAssignment visible latent)

/-- A closed rational identity saying that the alternating seven-cube
functional kills the product of the cubic slices indexed by `LatVar`. -/
def CubicWitnessProductBalance
    (LatVar : Type*) [Fintype LatVar] [DecidableEq LatVar] : Prop :=
  ∀ scopes : Assignment LatVar →
      FeatureScope (Sum (Fin 7) LatVar) 3,
    (∑ visible : BitVec 7,
      paritySevenDirectionRat visible *
        ∏ latent : Assignment LatVar,
          rationalMonomialValue (scopes latent).1
            (jointAssignment visible latent)) = 0

/-- With no hidden coordinates, this is the standard fact that the
alternating seven-cube trade kills every cubic monomial. -/
theorem cubicWitnessProductBalance_zeroHidden :
    CubicWitnessProductBalance (Fin 0) := by
  intro scopes
  simpa only [paritySevenDirectionRat_eq_evenParityDirectionRat] using
    sum_evenParityDirectionRat_mul_prod_rationalMonomialValue_eq_zero scopes
      (by decide)

/-- With one hidden bit, expanding the product of its two cubic slices gives
only visible monomials of degree at most six, all killed by the same trade. -/
theorem cubicWitnessProductBalance_oneHidden :
    CubicWitnessProductBalance (Fin 1) := by
  intro scopes
  simpa only [paritySevenDirectionRat_eq_evenParityDirectionRat] using
    sum_evenParityDirectionRat_mul_prod_rationalMonomialValue_eq_zero scopes
      (by decide)

/-- Compile the rational monomial identity into annihilation of the product
of arbitrary real cubic feature polynomials. -/
theorem sum_paritySevenDirection_mul_facialWitnessProduct_eq_zero
    {LatVar : Type*} [Fintype LatVar] [DecidableEq LatVar]
    (hBalance : CubicWitnessProductBalance LatVar)
    (energy : FeaturePolynomial (Sum (Fin 7) LatVar) 3) :
    (∑ visible : BitVec 7,
      paritySevenDirection visible *
        facialWitnessProduct energy visible) = 0 := by
  classical
  have hRealBalance : ∀ scopes : Assignment LatVar →
      FeatureScope (Sum (Fin 7) LatVar) 3,
      (∑ visible : BitVec 7,
        paritySevenDirection visible *
          ∏ latent : Assignment LatVar,
            monomialValue (scopes latent).1
              (jointAssignment visible latent)) = 0 := by
    intro scopes
    have hCast := congrArg (fun value : ℚ => (value : ℝ))
      (hBalance scopes)
    simpa [paritySevenDirection, Rat.cast_sum] using hCast
  unfold facialWitnessProduct FeaturePolynomial.eval
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scopes _
  simp_rw [Finset.prod_mul_distrib]
  calc
    (∑ visible : BitVec 7,
        paritySevenDirection visible *
          ((∏ latent : Assignment LatVar, energy (scopes latent)) *
            ∏ latent : Assignment LatVar,
              monomialValue (scopes latent).1
                (jointAssignment visible latent))) =
        (∏ latent : Assignment LatVar, energy (scopes latent)) *
          ∑ visible : BitVec 7,
            paritySevenDirection visible *
              ∏ latent : Assignment LatVar,
                monomialValue (scopes latent).1
                  (jointAssignment visible latent) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro visible _
      ring
    _ = 0 := by rw [hRealBalance scopes, mul_zero]

/-- A face exposing a lifted support yields a nonnegative witness product
which is zero precisely above visible support points. -/
theorem facialWitnessProduct_zero_iff
    {LatVar : Type*} [Fintype LatVar] [DecidableEq LatVar]
    {groundStates : Set (Assignment (Sum (Fin 7) LatVar))}
    (energy : FeaturePolynomial (Sum (Fin 7) LatVar) 3)
    (hZeroSet : ∀ joint, energy.eval joint = 0 ↔ joint ∈ groundStates)
    (visibleSupport : Set (BitVec 7))
    (hProjection : projectObs '' groundStates = visibleSupport)
    (visible : BitVec 7) :
    facialWitnessProduct energy visible = 0 ↔
      visible ∈ visibleSupport := by
  classical
  constructor
  · intro hProduct
    rw [facialWitnessProduct, Finset.prod_eq_zero_iff] at hProduct
    rcases hProduct with ⟨latent, _hLatent, hZero⟩
    rw [hZeroSet] at hZero
    rw [← hProjection]
    exact ⟨jointAssignment visible latent, hZero, rfl⟩
  · intro hVisible
    rw [← hProjection] at hVisible
    rcases hVisible with ⟨joint, hJoint, hProject⟩
    rw [facialWitnessProduct]
    apply Finset.prod_eq_zero (Finset.mem_univ (projectLat joint))
    have hDecompose :
        jointAssignment visible (projectLat joint) = joint := by
      rw [← hProject]
      exact jointAssignment_projectObs_projectLat joint
    rw [hDecompose]
    exact (hZeroSet joint).2 hJoint

theorem facialWitnessProduct_pos_of_not_mem
    {LatVar : Type*} [Fintype LatVar] [DecidableEq LatVar]
    {groundStates : Set (Assignment (Sum (Fin 7) LatVar))}
    (energy : FeaturePolynomial (Sum (Fin 7) LatVar) 3)
    (hNonnegative : ∀ joint, 0 ≤ energy.eval joint)
    (hZeroSet : ∀ joint, energy.eval joint = 0 ↔ joint ∈ groundStates)
    (visibleSupport : Set (BitVec 7))
    (hProjection : projectObs '' groundStates = visibleSupport)
    {visible : BitVec 7} (hOutside : visible ∉ visibleSupport) :
    0 < facialWitnessProduct energy visible := by
  classical
  rw [facialWitnessProduct]
  apply Finset.prod_pos
  intro latent _
  have hJointOutside :
      jointAssignment visible latent ∉ groundStates := by
    intro hJoint
    apply hOutside
    rw [← hProjection]
    exact ⟨jointAssignment visible latent, hJoint, rfl⟩
  have hNonzero :
      energy.eval (jointAssignment visible latent) ≠ 0 := by
    exact fun hZero => hJointOutside ((hZeroSet _).1 hZero)
  exact lt_of_le_of_ne (hNonnegative _) (Ne.symm hNonzero)

/-- The sign-definite parity contradiction, uniform in the latent type once
the corresponding finite degree-six balance identity is supplied. -/
theorem cubicWitnessProductBalance_obstructs_evenParitySeven
    {LatVar : Type*} [Fintype LatVar] [DecidableEq LatVar]
    (hBalance : CubicWitnessProductBalance LatVar) :
    ¬Nonempty (KLocalization 3 (Fin 7) LatVar
      evenParitySevenDistribution) := by
  rintro ⟨localization⟩
  let extension := localization.toGroundStateExtension
  rcases extension.facial with ⟨energy, hNonnegative, hZeroSet⟩
  have hProjection : projectObs '' extension.groundStates =
      (evenParitySeven : Set (BitVec 7)) := by
    calc
      projectObs '' extension.groundStates =
          evenParitySevenDistribution.support := extension.projection
      _ = (evenParitySeven : Set (BitVec 7)) :=
        evenParitySevenDistribution_support
  have hAnnihilates :=
    sum_paritySevenDirection_mul_facialWitnessProduct_eq_zero
      hBalance energy
  have hNonnegativeTerms : ∀ visible ∈ (Finset.univ : Finset (BitVec 7)),
      0 ≤ paritySevenDirection visible *
        facialWitnessProduct energy visible := by
    intro visible _
    cases hParity : paritySeven visible with
    | false =>
        have hMember : visible ∈ evenParitySeven := by
          simp [evenParitySeven, hParity]
        have hZero := (facialWitnessProduct_zero_iff energy
          hZeroSet _ hProjection visible).2 hMember
        simp [paritySevenDirection, paritySevenDirectionRat, hParity, hZero]
    | true =>
        have hOutside : visible ∉ evenParitySeven := by
          simp [evenParitySeven, hParity]
        have hPositive := facialWitnessProduct_pos_of_not_mem energy
          hNonnegative hZeroSet _ hProjection hOutside
        simpa [paritySevenDirection, paritySevenDirectionRat, hParity] using
          hPositive.le
  let allTrue : BitVec 7 := fun _ => true
  have hAllTrueParity : paritySeven allTrue = true := by decide +kernel
  have hAllTrueOutside : allTrue ∉ evenParitySeven := by
    simp [evenParitySeven, hAllTrueParity]
  have hAllTruePositive :
      0 < paritySevenDirection allTrue *
        facialWitnessProduct energy allTrue := by
    have hPositive := facialWitnessProduct_pos_of_not_mem energy
      hNonnegative hZeroSet _ hProjection hAllTrueOutside
    simpa [paritySevenDirection, paritySevenDirectionRat,
      hAllTrueParity] using hPositive
  have hPositiveSum : 0 < ∑ visible : BitVec 7,
      paritySevenDirection visible *
        facialWitnessProduct energy visible := by
    apply Finset.sum_pos' hNonnegativeTerms
    exact ⟨allTrue, Finset.mem_univ _, hAllTruePositive⟩
  rw [hAnnihilates] at hPositiveSum
  exact (lt_irrefl 0) hPositiveSum

theorem evenParitySeven_no_zeroHidden :
    ¬HasKLocalizationBits 3 0 7 evenParitySevenDistribution :=
  cubicWitnessProductBalance_obstructs_evenParitySeven
    cubicWitnessProductBalance_zeroHidden

theorem evenParitySeven_no_oneHidden :
    ¬HasKLocalizationBits 3 1 7 evenParitySevenDistribution :=
  cubicWitnessProductBalance_obstructs_evenParitySeven
    cubicWitnessProductBalance_oneHidden

/-- Hence the explicit even-parity law needs more than one hidden bit under
cubic localization. -/
theorem evenParitySeven_localizationComplexity_gt_one :
    1 < localizationComplexityBits 3 7 evenParitySevenDistribution := by
  rw [evenParitySevenDistribution_eq_evenParityDistribution]
  exact evenParity_cubic_localizationComplexity_gt (by norm_num)

/-! ## Matching two-hidden construction -/

/-- Integer coefficient vector for `W(x) - 2 h₀ - 4 h₁`. -/
def paritySevenWeightCoefficient : Sum (Fin 7) (Fin 2) → ℤ
  | Sum.inl _ => 1
  | Sum.inr hidden => if hidden = 0 then -2 else -4

/-- The displayed weighted linear form. -/
def paritySevenWeightedDifference
    (joint : Assignment (Sum (Fin 7) (Fin 2))) : ℤ :=
  ∑ coordinate : Sum (Fin 7) (Fin 2),
    paritySevenWeightCoefficient coordinate *
      QuadraticNAND.bitInt (joint coordinate)

/-- A computable enumeration of the nine lifted coordinates. -/
def paritySevenCoordinates : List (Sum (Fin 7) (Fin 2)) :=
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
    Sum.inl 5, Sum.inl 6, Sum.inr 0, Sum.inr 1]

/-- Syntactically quadratic expansion of the square of the weighted linear
form.  Ordered pairs make the expansion completely uniform. -/
def paritySevenSquarePolynomial :
    QuadraticNAND.QuadraticPolynomial (Sum (Fin 7) (Fin 2)) :=
  paritySevenCoordinates.flatMap fun left =>
    paritySevenCoordinates.map fun right => .pair
      (paritySevenWeightCoefficient left *
        paritySevenWeightCoefficient right) left right

theorem paritySevenSquarePolynomial_eval :
    ∀ joint : Assignment (Sum (Fin 7) (Fin 2)),
      paritySevenSquarePolynomial.eval joint =
        paritySevenWeightedDifference joint ^ 2 := by
  decide +kernel

theorem paritySevenSquarePolynomial_nonnegative
    (joint : Assignment (Sum (Fin 7) (Fin 2))) :
    0 ≤ paritySevenSquarePolynomial.eval joint := by
  rw [paritySevenSquarePolynomial_eval]
  positivity

/-- The computable zero set of the Hamming-weight square. -/
def paritySevenLiftedSet :
    Finset (Assignment (Sum (Fin 7) (Fin 2))) :=
  Finset.univ.filter fun joint => paritySevenWeightedDifference joint = 0

theorem paritySevenLiftedSet_nonempty :
    paritySevenLiftedSet.Nonempty := by
  decide +kernel

theorem paritySevenLiftedSet_mapsTo :
    ∀ joint ∈ paritySevenLiftedSet,
      projectObs joint ∈ evenParitySeven := by
  have hParity : ∀ joint : Assignment (Sum (Fin 7) (Fin 2)),
      paritySevenWeightedDifference joint = 0 → paritySeven (projectObs joint) = false := by
    decide +kernel
  intro joint hJoint
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hParity joint (Finset.mem_filter.mp hJoint).2⟩

/-- Hamming weight of a visible seven-bit assignment. -/
def paritySevenVisibleWeight (visible : BitVec 7) : Nat :=
  ∑ coordinate : Fin 7, if visible coordinate then 1 else 0

/-- The two-bit binary encoding of half the (even) visible Hamming weight. -/
def paritySevenLatentExtension (visible : BitVec 7) : Assignment (Fin 2) :=
  fun hidden =>
    if hidden = 0 then
      decide (paritySevenVisibleWeight visible % 4 = 2)
    else
      decide (4 ≤ paritySevenVisibleWeight visible)

/-- The canonical lifted assignment above an even-parity visible string. -/
def paritySevenJointExtension
    (visible : BitVec 7) : Assignment (Sum (Fin 7) (Fin 2)) :=
  jointAssignment visible (paritySevenLatentExtension visible)

theorem paritySevenJointExtension_mem :
    ∀ visible ∈ evenParitySeven,
      paritySevenJointExtension visible ∈ paritySevenLiftedSet := by
  have hZero : ∀ visible : BitVec 7,
      paritySeven visible = false →
        paritySevenWeightedDifference (paritySevenJointExtension visible) = 0 := by
    decide +kernel
  intro visible hVisible
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZero visible (Finset.mem_filter.mp hVisible).2⟩

theorem paritySevenJointExtension_unique :
    ∀ visible ∈ evenParitySeven,
      ∀ joint ∈ paritySevenLiftedSet,
        projectObs joint = visible →
          joint = paritySevenJointExtension visible := by
  have hUnique : ∀ visible : BitVec 7, ∀ latent : Assignment (Fin 2),
      paritySeven visible = false →
        paritySevenWeightedDifference (jointAssignment visible latent) = 0 →
          jointAssignment visible latent = paritySevenJointExtension visible := by
    decide +kernel
  intro visible hVisible joint hJoint hObs
  have hDecompose : jointAssignment visible (projectLat joint) = joint := by
    rw [← hObs]
    exact jointAssignment_projectObs_projectLat joint
  have hZero := (Finset.mem_filter.mp hJoint).2
  rw [← hDecompose] at hZero ⊢
  exact hUnique visible (projectLat joint) (Finset.mem_filter.mp hVisible).2 hZero

theorem paritySevenLiftedSet_uniqueExtension :
    ∀ visible ∈ evenParitySeven,
      ∃! joint, joint ∈ paritySevenLiftedSet ∧
        projectObs joint = visible := by
  intro visible hVisible
  refine ⟨paritySevenJointExtension visible, ?_, ?_⟩
  · exact ⟨paritySevenJointExtension_mem visible hVisible,
      projectObs_jointAssignment visible
        (paritySevenLatentExtension visible)⟩
  · intro joint hJoint
    exact paritySevenJointExtension_unique visible hVisible
      joint hJoint.1 hJoint.2

theorem paritySevenLiftedSet_is_groundSpace
    (joint : Assignment (Sum (Fin 7) (Fin 2))) :
    joint ∈ paritySevenLiftedSet ↔
      localEnergyEval paritySevenSquarePolynomial.toLocalEnergy joint = 0 := by
  rw [paritySevenSquarePolynomial.localEnergyEval_toLocalEnergy,
    paritySevenSquarePolynomial_eval]
  simp [paritySevenLiftedSet]

theorem paritySevenSquare_isMarginalModel :
    IsMarginalModel evenParitySevenDistribution
      (uniformOn paritySevenLiftedSet paritySevenLiftedSet_nonempty) := by
  exact uniformOn_isMarginalModel_of_unique_extension
    paritySevenLiftedSet
    paritySevenLiftedSet_nonempty
    evenParitySeven evenParitySeven_nonempty
    paritySevenLiftedSet_mapsTo
    paritySevenLiftedSet_uniqueExtension

/-- The Hamming-weight square gives the matching two-hidden cubic
localization (in fact its lifted law is already quadratic). -/
theorem evenParitySeven_has_twoHidden :
    HasKLocalizationBits 3 2 7 evenParitySevenDistribution := by
  apply hasKLocalizationBits_of_localEnergyGroundStates
    paritySevenLiftedSet paritySevenLiftedSet_nonempty
    paritySevenSquarePolynomial.toLocalEnergy
  · intro term hTerm
    exact Nat.le_trans
      (paritySevenSquarePolynomial.toLocalEnergy_respects_two term hTerm)
      (by omega)
  · intro joint
    rw [paritySevenSquarePolynomial.localEnergyEval_toLocalEnergy]
    exact_mod_cast paritySevenSquarePolynomial_nonnegative joint
  · exact paritySevenLiftedSet_is_groundSpace
  · exact paritySevenSquare_isMarginalModel

/-- Exact nontrivial cubic localization complexity of an explicit law. -/
theorem evenParitySeven_localizationComplexity_eq_two :
    localizationComplexityBits 3 7 evenParitySevenDistribution = 2 := by
  have hUpper := localizationComplexityBits_min 3 7
    evenParitySevenDistribution 2 evenParitySeven_has_twoHidden
  have hLower := evenParitySeven_localizationComplexity_gt_one
  omega

end KLocality
