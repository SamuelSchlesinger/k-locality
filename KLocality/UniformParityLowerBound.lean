import KLocality.WitnessProductCertificate

namespace KLocality

open scoped BigOperators

/-!
# Uniform parity lower bounds

This module proves the natural-number-parameterized witness-product lower
bound for parity.  If an order-`k` localization of the uniform even-parity law
on `n` visible bits uses `ell` hidden bits, then `k * 2^ell >= n`.

The proof keeps the finite argument structural.  The product of all hidden
slices expands into products of order-`k` monomials.  Across all hidden
assignments such a product touches at most `k * 2^ell` visible coordinates.
When this is less than `n`, flipping an untouched coordinate negates the
parity character without changing the monomial product, so the alternating
cube sum vanishes.  Nonnegativity and the exposed zero set force the same sum
to be strictly positive, a contradiction.
-/

/-! ## The parity character and coordinate flips -/

/-- One factor in the alternating Boolean-cube character. -/
def parityCoordinateSign (bit : Bool) : ℚ :=
  if bit then -1 else 1

@[simp]
theorem parityCoordinateSign_false : parityCoordinateSign false = 1 := rfl

@[simp]
theorem parityCoordinateSign_true : parityCoordinateSign true = -1 := rfl

theorem parityCoordinateSign_ne_zero (bit : Bool) :
    parityCoordinateSign bit ≠ 0 := by
  cases bit <;> norm_num

/-- Alternating character, with sign `-1` on even weight and `+1` on odd
weight. -/
def evenParityDirectionRat (n : Nat) (visible : BitVec n) : ℚ :=
  -(∏ coordinate : Fin n, parityCoordinateSign (visible coordinate))

/-- Real embedding of the alternating character. -/
noncomputable def evenParityDirection (n : Nat) (visible : BitVec n) : ℝ :=
  evenParityDirectionRat n visible

theorem evenParityDirectionRat_ne_zero (n : Nat) (visible : BitVec n) :
    evenParityDirectionRat n visible ≠ 0 := by
  unfold evenParityDirectionRat
  exact neg_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun coordinate _ =>
    parityCoordinateSign_ne_zero (visible coordinate))

/-- The all-false assignment. -/
def allFalseBitVec (n : Nat) : BitVec n := fun _ => false

@[simp]
theorem evenParityDirectionRat_allFalse (n : Nat) :
    evenParityDirectionRat n (allFalseBitVec n) = -1 := by
  simp [evenParityDirectionRat, allFalseBitVec]

/-- Flip one visible coordinate. -/
def flipBit {n : Nat} (coordinate : Fin n) (visible : BitVec n) : BitVec n :=
  fun candidate =>
    if candidate = coordinate then !visible candidate else visible candidate

@[simp]
theorem flipBit_apply_self {n : Nat} (coordinate : Fin n)
    (visible : BitVec n) :
    flipBit coordinate visible coordinate = !visible coordinate := by
  simp [flipBit]

theorem flipBit_apply_of_ne {n : Nat} {coordinate candidate : Fin n}
    (hNe : candidate ≠ coordinate) (visible : BitVec n) :
    flipBit coordinate visible candidate = visible candidate := by
  simp [flipBit, hNe]

@[simp]
theorem flipBit_involution {n : Nat} (coordinate : Fin n)
    (visible : BitVec n) :
    flipBit coordinate (flipBit coordinate visible) = visible := by
  funext candidate
  by_cases hCandidate : candidate = coordinate
  · subst candidate
    simp
  · simp [flipBit_apply_of_ne hCandidate]

/-- Flipping a fixed bit is an equivalence of the Boolean cube. -/
def flipBitEquiv {n : Nat} (coordinate : Fin n) : BitVec n ≃ BitVec n where
  toFun := flipBit coordinate
  invFun := flipBit coordinate
  left_inv := flipBit_involution coordinate
  right_inv := flipBit_involution coordinate

theorem evenParityDirectionRat_flipBit {n : Nat} (coordinate : Fin n)
    (visible : BitVec n) :
    evenParityDirectionRat n (flipBit coordinate visible) =
      -evenParityDirectionRat n visible := by
  classical
  unfold evenParityDirectionRat
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
      (fun candidate => parityCoordinateSign
        (flipBit coordinate visible candidate)) (Finset.mem_univ coordinate)]
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
      (fun candidate => parityCoordinateSign (visible candidate))
      (Finset.mem_univ coordinate)]
  have hOutside :
      (∏ candidate ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
          parityCoordinateSign (flipBit coordinate visible candidate)) =
        ∏ candidate ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
          parityCoordinateSign (visible candidate) := by
    apply Finset.prod_congr rfl
    intro candidate hCandidate
    rw [flipBit_apply_of_ne (Finset.ne_of_mem_erase hCandidate)]
  rw [hOutside, flipBit_apply_self]
  cases visible coordinate <;> norm_num

/-! ## Visible coordinates used by a family of feature scopes -/

/-- Union of the observed parts of a scope chosen for every hidden
assignment. -/
def observedCoordinatesUsed
    {k n : Nat} {LatVar : Type*}
    [Fintype LatVar] [DecidableEq LatVar]
    (scopes : Assignment LatVar → FeatureScope (Sum (Fin n) LatVar) k) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Assignment LatVar)).biUnion fun latent =>
    (scopes latent).1.toLeft

theorem card_observedCoordinatesUsed_le
    {k n : Nat} {LatVar : Type*}
    [Fintype LatVar] [DecidableEq LatVar]
    (scopes : Assignment LatVar → FeatureScope (Sum (Fin n) LatVar) k) :
    (observedCoordinatesUsed scopes).card ≤
      k * Fintype.card (Assignment LatVar) := by
  classical
  have hBound := Finset.card_biUnion_le_card_mul
    (Finset.univ : Finset (Assignment LatVar))
    (fun latent => (scopes latent).1.toLeft) k
    (fun latent _ =>
      Finset.card_toLeft_le.trans (scopes latent).2)
  simpa [observedCoordinatesUsed, Nat.mul_comm] using hBound

theorem exists_observedCoordinate_not_used
    {k n : Nat} {LatVar : Type*}
    [Fintype LatVar] [DecidableEq LatVar]
    (scopes : Assignment LatVar → FeatureScope (Sum (Fin n) LatVar) k)
    (hSize : k * Fintype.card (Assignment LatVar) < n) :
    ∃ coordinate : Fin n,
      ∀ latent : Assignment LatVar,
        Sum.inl coordinate ∉ (scopes latent).1 := by
  classical
  have hCard : (observedCoordinatesUsed scopes).card <
      (Finset.univ : Finset (Fin n)).card := by
    calc
      (observedCoordinatesUsed scopes).card ≤
          k * Fintype.card (Assignment LatVar) :=
        card_observedCoordinatesUsed_le scopes
      _ < n := hSize
      _ = (Finset.univ : Finset (Fin n)).card := by simp
  rcases Finset.exists_mem_notMem_of_card_lt_card hCard with
    ⟨coordinate, _hCoordinate, hUnused⟩
  refine ⟨coordinate, ?_⟩
  intro latent hMember
  apply hUnused
  simp only [observedCoordinatesUsed, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_toLeft]
  exact ⟨latent, hMember⟩

/-! ## Alternating-cube annihilation -/

/-- Flipping a coordinate outside a monomial scope leaves that monomial
unchanged. -/
theorem rationalMonomialValue_flipBit_of_not_mem
    {n : Nat} (scope : Finset (Fin n)) (visible : BitVec n)
    (coordinate : Fin n) (hUnused : coordinate ∉ scope) :
    rationalMonomialValue scope (flipBit coordinate visible) =
      rationalMonomialValue scope visible := by
  unfold rationalMonomialValue
  congr 1
  apply propext
  constructor
  · intro hSubset candidate hCandidate
    apply (mem_trueCoordinates visible candidate).2
    have hTrue := (mem_trueCoordinates
      (flipBit coordinate visible) candidate).1 (hSubset hCandidate)
    by_cases hSame : candidate = coordinate
    · subst candidate
      exact False.elim (hUnused hCandidate)
    · simpa [flipBit_apply_of_ne hSame] using hTrue
  · intro hSubset candidate hCandidate
    apply (mem_trueCoordinates (flipBit coordinate visible) candidate).2
    have hTrue :=
      (mem_trueCoordinates visible candidate).1 (hSubset hCandidate)
    by_cases hSame : candidate = coordinate
    · subst candidate
      exact False.elim (hUnused hCandidate)
    · simpa [flipBit_apply_of_ne hSame] using hTrue

/-- The alternating character annihilates every individual monomial whose
degree is strictly below the cube dimension. -/
theorem sum_evenParityDirectionRat_mul_rationalMonomialValue_eq_zero
    {k n : Nat} (scope : FeatureScope (Fin n) k) (hSize : k < n) :
    (∑ visible : BitVec n,
      evenParityDirectionRat n visible *
        rationalMonomialValue scope.1 visible) = 0 := by
  classical
  have hCard : scope.1.card <
      (Finset.univ : Finset (Fin n)).card := by
    simpa using lt_of_le_of_lt scope.2 hSize
  rcases Finset.exists_mem_notMem_of_card_lt_card hCard with
    ⟨coordinate, _hCoordinate, hUnused⟩
  let summand : BitVec n → ℚ := fun visible =>
    evenParityDirectionRat n visible *
      rationalMonomialValue scope.1 visible
  have hSummandFlip : ∀ visible : BitVec n,
      summand (flipBit coordinate visible) = -summand visible := by
    intro visible
    simp only [summand, evenParityDirectionRat_flipBit]
    rw [rationalMonomialValue_flipBit_of_not_mem
      scope.1 visible coordinate hUnused]
    ring
  have hReindex := (flipBitEquiv coordinate).sum_comp summand
  have hNeg : (∑ visible : BitVec n, summand visible) =
      -(∑ visible : BitVec n, summand visible) := by
    calc
      (∑ visible : BitVec n, summand visible) =
          ∑ visible : BitVec n, summand (flipBit coordinate visible) :=
        hReindex.symm
      _ = ∑ visible : BitVec n, -summand visible := by
        apply Finset.sum_congr rfl
        intro visible _
        exact hSummandFlip visible
      _ = -(∑ visible : BitVec n, summand visible) := by
        rw [Finset.sum_neg_distrib]
  have hZero : (∑ visible : BitVec n, summand visible) = 0 := by
    linarith
  exact hZero

/-- The alternating character has total mass zero on every nontrivial Boolean
cube. -/
theorem sum_evenParityDirectionRat_eq_zero
    {n : Nat} (hn : 0 < n) :
    (∑ visible : BitVec n, evenParityDirectionRat n visible) = 0 := by
  let empty : FeatureScope (Fin n) 0 := ⟨∅, by simp⟩
  have hBalance :=
    sum_evenParityDirectionRat_mul_rationalMonomialValue_eq_zero
      empty hn
  simpa [rationalMonomialValue] using hBalance

theorem rationalMonomialValue_joint_flipBit_of_not_mem
    {k n : Nat} {LatVar : Type*}
    [Fintype LatVar] [DecidableEq LatVar]
    (scope : FeatureScope (Sum (Fin n) LatVar) k)
    (latent : Assignment LatVar) (visible : BitVec n)
    (coordinate : Fin n) (hUnused : Sum.inl coordinate ∉ scope.1) :
    rationalMonomialValue scope.1
        (jointAssignment (flipBit coordinate visible) latent) =
      rationalMonomialValue scope.1 (jointAssignment visible latent) := by
  unfold rationalMonomialValue
  congr 1
  apply propext
  constructor
  · intro hSubset candidateVariable hVariable
    apply (mem_trueCoordinates _ candidateVariable).2
    have hTrue :=
      (mem_trueCoordinates _ candidateVariable).1 (hSubset hVariable)
    cases candidateVariable with
    | inl candidate =>
        simp only [jointAssignment_apply_observed] at hTrue ⊢
        by_cases hCandidate : candidate = coordinate
        · subst candidate
          exact False.elim (hUnused hVariable)
        · simpa [flipBit_apply_of_ne hCandidate] using hTrue
    | inr hidden =>
        simpa using hTrue
  · intro hSubset candidateVariable hVariable
    apply (mem_trueCoordinates _ candidateVariable).2
    have hTrue :=
      (mem_trueCoordinates _ candidateVariable).1 (hSubset hVariable)
    cases candidateVariable with
    | inl candidate =>
        simp only [jointAssignment_apply_observed] at hTrue ⊢
        by_cases hCandidate : candidate = coordinate
        · subst candidate
          exact False.elim (hUnused hVariable)
        · simpa [flipBit_apply_of_ne hCandidate] using hTrue
    | inr hidden =>
        simpa using hTrue

/-- Products of feature monomials involving fewer than `n` visible
coordinates are killed by the alternating character. -/
theorem sum_evenParityDirectionRat_mul_prod_rationalMonomialValue_eq_zero
    {k n : Nat} {LatVar : Type*}
    [Fintype LatVar] [DecidableEq LatVar]
    (scopes : Assignment LatVar → FeatureScope (Sum (Fin n) LatVar) k)
    (hSize : k * Fintype.card (Assignment LatVar) < n) :
    (∑ visible : BitVec n,
      evenParityDirectionRat n visible *
        ∏ latent : Assignment LatVar,
          rationalMonomialValue (scopes latent).1
            (jointAssignment visible latent)) = 0 := by
  classical
  rcases exists_observedCoordinate_not_used scopes hSize with
    ⟨coordinate, hUnused⟩
  let summand : BitVec n → ℚ := fun visible =>
    evenParityDirectionRat n visible *
      ∏ latent : Assignment LatVar,
        rationalMonomialValue (scopes latent).1
          (jointAssignment visible latent)
  have hProductFlip : ∀ visible : BitVec n,
      (∏ latent : Assignment LatVar,
          rationalMonomialValue (scopes latent).1
            (jointAssignment (flipBit coordinate visible) latent)) =
        ∏ latent : Assignment LatVar,
          rationalMonomialValue (scopes latent).1
            (jointAssignment visible latent) := by
    intro visible
    apply Finset.prod_congr rfl
    intro latent _
    exact rationalMonomialValue_joint_flipBit_of_not_mem
      (scopes latent) latent visible coordinate (hUnused latent)
  have hSummandFlip : ∀ visible : BitVec n,
      summand (flipBit coordinate visible) = -summand visible := by
    intro visible
    simp only [summand, evenParityDirectionRat_flipBit, hProductFlip]
    ring
  have hReindex := (flipBitEquiv coordinate).sum_comp summand
  have hNeg : (∑ visible : BitVec n, summand visible) =
      -(∑ visible : BitVec n, summand visible) := by
    calc
      (∑ visible : BitVec n, summand visible) =
          ∑ visible : BitVec n, summand (flipBit coordinate visible) :=
        hReindex.symm
      _ = ∑ visible : BitVec n, -summand visible := by
        apply Finset.sum_congr rfl
        intro visible _
        exact hSummandFlip visible
      _ = -(∑ visible : BitVec n, summand visible) := by
        rw [Finset.sum_neg_distrib]
  have hZero : (∑ visible : BitVec n, summand visible) = 0 := by
    linarith
  exact hZero

/-! ## The uniform even-parity law -/

/-- Even-parity strings, characterized by the negative half of the
alternating character. -/
def evenParitySupport (n : Nat) : Finset (BitVec n) :=
  Finset.univ.filter fun visible => evenParityDirectionRat n visible < 0

theorem evenParitySupport_nonempty (n : Nat) :
    (evenParitySupport n).Nonempty := by
  refine ⟨allFalseBitVec n, ?_⟩
  simp [evenParitySupport]

/-- Uniform distribution on the even-parity strings of length `n`. -/
noncomputable def evenParityDistribution (n : Nat) : Distribution (BitVec n) :=
  uniformOn (evenParitySupport n) (evenParitySupport_nonempty n)

@[simp]
theorem evenParityDistribution_support (n : Nat) :
    (evenParityDistribution n).support =
      (evenParitySupport n : Set (BitVec n)) := by
  simp [evenParityDistribution]

/-! ## The uniform witness-product certificate -/

/-- The parity character gives a sign-definite witness-product certificate
whenever all hidden slices together touch fewer than `n` visible
coordinates. -/
def evenParityWitnessProductCertificate
    {k n : Nat} {LatVar : Type*}
    [Fintype LatVar] [DecidableEq LatVar]
    (hSize : k * Fintype.card (Assignment LatVar) < n) :
    WitnessProductCertificate k (Fin n) LatVar
      (evenParitySupport n : Set (BitVec n)) where
  direction := evenParityDirectionRat n
  monomialBalance := fun scopes =>
    sum_evenParityDirectionRat_mul_prod_rationalMonomialValue_eq_zero
      scopes hSize
  nonnegativeOutside := by
    intro visible hOutside
    have hNotNegative : ¬evenParityDirectionRat n visible < 0 := by
      simpa [evenParitySupport] using hOutside
    exact le_of_not_gt hNotNegative
  positiveOutside := by
    have hnPositive : 0 < n := by omega
    let coordinate : Fin n := ⟨0, hnPositive⟩
    let oddVisible : BitVec n := flipBit coordinate (allFalseBitVec n)
    have hOddDirection : evenParityDirectionRat n oddVisible = 1 := by
      simp [oddVisible, evenParityDirectionRat_flipBit]
    refine ⟨oddVisible, ?_, ?_⟩
    · simp [evenParitySupport, hOddDirection]
    · rw [hOddDirection]
      norm_num

/-- Uniform sign-definite obstruction for an arbitrary finite hidden type. -/
theorem noKLocalization_evenParity_of_card_lt
    {k n : Nat} {LatVar : Type*}
    [Fintype LatVar] [DecidableEq LatVar]
    (hSize : k * Fintype.card (Assignment LatVar) < n) :
    ¬Nonempty (KLocalization k (Fin n) LatVar
      (evenParityDistribution n)) :=
  (evenParityWitnessProductCertificate hSize).obstructs_localization
    (evenParityDistribution n) (evenParityDistribution_support n)

/-- A `k`-localization of even parity with `ell` hidden bits must satisfy the
witness-product size inequality `n ≤ k * 2^ell`. -/
theorem evenParity_size_le_of_hasKLocalization
    {k n ell : Nat}
    (localization : HasKLocalizationBits k ell n
      (evenParityDistribution n)) :
    n ≤ k * 2 ^ ell := by
  by_contra hNot
  have hSize : k * Fintype.card (Assignment (Fin ell)) < n := by
    simpa [Assignment, Fintype.card_fun] using Nat.lt_of_not_ge hNot
  exact noKLocalization_evenParity_of_card_lt hSize localization

/-- Uniform lower bound in contrapositive form. -/
theorem evenParity_no_kLocalization_of_lt
    {k n ell : Nat} (hSize : k * 2 ^ ell < n) :
    ¬HasKLocalizationBits k ell n (evenParityDistribution n) := by
  intro localization
  have hNecessary := evenParity_size_le_of_hasKLocalization localization
  omega

/-- Uniform localization-complexity lower bound for parity. -/
theorem evenParity_localizationComplexity_gt
    {k n ell : Nat} (hk : 2 ≤ k) (hSize : k * 2 ^ ell < n) :
    ell < localizationComplexityBits k n (evenParityDistribution n) := by
  have hExists := kLocalization_exists (evenParityDistribution n) hk
  have hOptimal := localizationComplexityBits_spec
    k n (evenParityDistribution n) hExists
  by_contra hNot
  have hAtMost : localizationComplexityBits k n
      (evenParityDistribution n) ≤ ell := Nat.le_of_not_gt hNot
  have hPow : 2 ^ localizationComplexityBits k n
      (evenParityDistribution n) ≤ 2 ^ ell := by
    gcongr
    norm_num
  have hSizeOptimal :
      k * 2 ^ localizationComplexityBits k n (evenParityDistribution n) < n :=
    lt_of_le_of_lt (Nat.mul_le_mul_left k hPow) hSize
  exact evenParity_no_kLocalization_of_lt hSizeOptimal hOptimal

/-- Cubic specialization: `3 * 2^ell < n` forces more than `ell` hidden
bits. -/
theorem evenParity_cubic_localizationComplexity_gt
    {n ell : Nat} (hSize : 3 * 2 ^ ell < n) :
    ell < localizationComplexityBits 3 n (evenParityDistribution n) :=
  evenParity_localizationComplexity_gt (by omega) hSize

end KLocality
