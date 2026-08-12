import KLocality.UniformParityLowerBound
import KLocality.GroundStateProjection
import KLocality.QuadraticNAND

namespace KLocality

open scoped BigOperators

/-!
# Uniform parity upper bounds

This module constructs the matching logarithmic lift for the uniform
even-parity family.  The hidden assignment encodes half the visible Hamming
weight in binary, and the quadratic energy is the square of

`W(x) - 2 * J(h)`.
-/

/-! ## Hamming weight and binary hidden values -/

/-- Hamming weight of a Boolean assignment. -/
def assignmentWeight {Var : Type*} [Fintype Var]
    (assignment : Assignment Var) : Nat :=
  ∑ coordinate : Var, (assignment coordinate).toNat

/-- Value of a little-endian binary assignment. -/
def binaryAssignmentValue {ell : Nat}
    (assignment : Assignment (Fin ell)) : Nat :=
  ∑ coordinate : Fin ell,
    2 ^ coordinate.val * (assignment coordinate).toNat

theorem binaryAssignmentValue_succ {ell : Nat}
    (assignment : Assignment (Fin (ell + 1))) :
    binaryAssignmentValue assignment =
      binaryAssignmentValue
          (fun coordinate : Fin ell => assignment coordinate.castSucc) +
        2 ^ ell * (assignment (Fin.last ell)).toNat := by
  simp [binaryAssignmentValue, Fin.sum_univ_castSucc]

theorem binaryAssignmentValue_lt_two_pow :
    ∀ {ell : Nat} (assignment : Assignment (Fin ell)),
      binaryAssignmentValue assignment < 2 ^ ell := by
  intro ell
  induction ell with
  | zero =>
      intro assignment
      simp [binaryAssignmentValue]
  | succ ell ih =>
      intro assignment
      rw [binaryAssignmentValue_succ]
      have hLower := ih
        (fun coordinate : Fin ell => assignment coordinate.castSucc)
      cases hBit : assignment (Fin.last ell) <;>
        simp [Nat.pow_succ] <;> omega

/-- The low `ell` binary digits of a natural number. -/
def binaryAssignment (ell value : Nat) : Assignment (Fin ell) :=
  fun coordinate => value.testBit coordinate.val

theorem binaryAssignmentValue_binaryAssignment (ell value : Nat) :
    binaryAssignmentValue (binaryAssignment ell value) = value % 2 ^ ell := by
  induction ell with
  | zero =>
      change 0 = value % 1
      omega
  | succ ell ih =>
      rw [binaryAssignmentValue_succ]
      have hRestriction :
          (fun coordinate : Fin ell =>
            binaryAssignment (ell + 1) value coordinate.castSucc) =
            binaryAssignment ell value := rfl
      rw [hRestriction, ih]
      change value % 2 ^ ell + 2 ^ ell * (value.testBit ell).toNat =
        value % 2 ^ (ell + 1)
      rw [Nat.mod_pow_succ, Nat.toNat_testBit]

theorem binaryAssignmentValue_binaryAssignment_of_lt
    {ell value : Nat} (hValue : value < 2 ^ ell) :
    binaryAssignmentValue (binaryAssignment ell value) = value := by
  rw [binaryAssignmentValue_binaryAssignment, Nat.mod_eq_of_lt hValue]

theorem binaryAssignmentValue_injective (ell : Nat) :
    Function.Injective
      (binaryAssignmentValue : Assignment (Fin ell) → Nat) := by
  induction ell with
  | zero =>
      intro left right _
      funext coordinate
      exact Fin.elim0 coordinate
  | succ ell ih =>
      intro left right hValue
      have hExpanded := hValue
      rw [binaryAssignmentValue_succ, binaryAssignmentValue_succ] at hExpanded
      have hLeftBound := binaryAssignmentValue_lt_two_pow
        (fun coordinate : Fin ell => left coordinate.castSucc)
      have hRightBound := binaryAssignmentValue_lt_two_pow
        (fun coordinate : Fin ell => right coordinate.castSucc)
      have hLast : left (Fin.last ell) = right (Fin.last ell) := by
        cases hLeft : left (Fin.last ell) <;>
          cases hRight : right (Fin.last ell)
        · rfl
        · simp [hLeft, hRight] at hExpanded
          omega
        · simp [hLeft, hRight] at hExpanded
          omega
        · rfl
      have hLower :
          (fun coordinate : Fin ell => left coordinate.castSucc) =
            fun coordinate : Fin ell => right coordinate.castSucc := by
        apply ih
        rw [hLast] at hExpanded
        omega
      funext coordinate
      exact Fin.lastCases hLast
        (fun lower => congrFun hLower lower) coordinate

/-! ## Parity as even Hamming weight -/

theorem prod_parityCoordinateSign_eq_neg_one_pow
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (assignment : Assignment Var) :
    (∏ coordinate : Var, parityCoordinateSign (assignment coordinate)) =
      (-1 : ℚ) ^ assignmentWeight assignment := by
  classical
  unfold assignmentWeight
  induction (Finset.univ : Finset Var) using Finset.induction_on with
  | empty => simp
  | @insert coordinate coordinates hCoordinate ih =>
      rw [Finset.prod_insert hCoordinate, Finset.sum_insert hCoordinate,
        pow_add, ih]
      cases assignment coordinate <;> norm_num

theorem mem_evenParitySupport_iff_even_weight {n : Nat}
    (visible : BitVec n) :
    visible ∈ evenParitySupport n ↔ Even (assignmentWeight visible) := by
  rw [evenParitySupport, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, evenParityDirectionRat]
  rw [prod_parityCoordinateSign_eq_neg_one_pow]
  by_cases hEven : Even (assignmentWeight visible) <;>
    simp [neg_one_pow_eq_ite, hEven]

/-! ## A generic syntactic square of a linear form -/

/-- Ordered-pair expansion of the square of an integer linear form. -/
noncomputable def linearFormSquarePolynomial
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (coefficient : Var → ℤ) : QuadraticNAND.QuadraticPolynomial Var :=
  (Finset.univ : Finset Var).toList.flatMap fun left =>
    (Finset.univ : Finset Var).toList.map fun right =>
      .pair (coefficient left * coefficient right) left right

theorem linearFormSquarePolynomial_eval
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (coefficient : Var → ℤ) (assignment : Assignment Var) :
    (linearFormSquarePolynomial coefficient).eval assignment =
      (∑ coordinate : Var,
        coefficient coordinate * QuadraticNAND.bitInt (assignment coordinate)) ^ 2 := by
  classical
  let coordinates := (Finset.univ : Finset Var).toList
  let value : Var → ℤ := fun coordinate =>
    coefficient coordinate * QuadraticNAND.bitInt (assignment coordinate)
  have hInner : ∀ left : Var,
      QuadraticNAND.QuadraticPolynomial.eval assignment
        (coordinates.map fun right =>
          QuadraticNAND.QuadraticTerm.pair
            (coefficient left * coefficient right) left right) =
        value left * (coordinates.map value).sum := by
    intro left
    simp only [QuadraticNAND.QuadraticPolynomial.eval, List.map_map]
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro right _
    simp only [Function.comp_apply, QuadraticNAND.QuadraticTerm.eval, value]
    ring
  unfold linearFormSquarePolynomial
  rw [QuadraticNAND.QuadraticPolynomial.eval_flatMap]
  change (coordinates.map fun left =>
    QuadraticNAND.QuadraticPolynomial.eval assignment
      (coordinates.map fun right =>
        QuadraticNAND.QuadraticTerm.pair
          (coefficient left * coefficient right) left right)).sum = _
  simp_rw [hInner]
  rw [List.sum_map_mul_right]
  have hCoordinates : (coordinates.map value).sum =
      ∑ coordinate : Var, value coordinate := by
    simp [coordinates]
  rw [hCoordinates]
  simp only [value]
  ring

/-! ## The Hamming-weight square -/

@[simp]
theorem bitInt_eq_intCast_toNat (bit : Bool) :
    QuadraticNAND.bitInt bit = (bit.toNat : ℤ) := by
  cases bit <;> rfl

/-- Coefficients of `W(x) - 2 * J(h)`. -/
def parityLiftCoefficient {n ell : Nat} :
    Sum (Fin n) (Fin ell) → ℤ
  | Sum.inl _ => 1
  | Sum.inr hidden => -(2 : ℤ) ^ (hidden.val + 1)

/-- Integer linear form whose square exposes the parity lift. -/
def parityLiftLinearValue {n ell : Nat}
    (joint : Assignment (Sum (Fin n) (Fin ell))) : ℤ :=
  ∑ coordinate : Sum (Fin n) (Fin ell),
    parityLiftCoefficient coordinate *
      QuadraticNAND.bitInt (joint coordinate)

theorem parityLiftLinearValue_eq {n ell : Nat}
    (joint : Assignment (Sum (Fin n) (Fin ell))) :
    parityLiftLinearValue joint =
      (assignmentWeight (projectObs joint) : ℤ) -
        2 * (binaryAssignmentValue (projectLat joint) : ℤ) := by
  rw [parityLiftLinearValue, Fintype.sum_sum_type]
  simp only [parityLiftCoefficient, assignmentWeight, projectObs, projectLat,
    bitInt_eq_intCast_toNat, binaryAssignmentValue, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [pow_succ]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro visible _
    ring
  · calc
      (∑ hidden : Fin ell,
          -(2 ^ hidden.val * 2 : ℤ) *
            (joint (Sum.inr hidden)).toNat) =
          ∑ hidden : Fin ell,
            -(2 * (2 ^ hidden.val *
              (joint (Sum.inr hidden)).toNat) : ℤ) := by
        apply Finset.sum_congr rfl
        intro hidden _
        ring
      _ = -(∑ hidden : Fin ell,
          2 * (2 ^ hidden.val *
            (joint (Sum.inr hidden)).toNat) : ℤ) := by
        rw [Finset.sum_neg_distrib]

/-- Syntactic quadratic expansion of the Hamming-weight square. -/
noncomputable def parityLiftSquarePolynomial (n ell : Nat) :
    QuadraticNAND.QuadraticPolynomial (Sum (Fin n) (Fin ell)) :=
  linearFormSquarePolynomial
    (parityLiftCoefficient : Sum (Fin n) (Fin ell) → ℤ)

theorem parityLiftSquarePolynomial_eval {n ell : Nat}
    (joint : Assignment (Sum (Fin n) (Fin ell))) :
    (parityLiftSquarePolynomial n ell).eval joint =
      parityLiftLinearValue joint ^ 2 := by
  exact linearFormSquarePolynomial_eval parityLiftCoefficient joint

theorem parityLiftSquarePolynomial_nonnegative {n ell : Nat}
    (joint : Assignment (Sum (Fin n) (Fin ell))) :
    0 ≤ (parityLiftSquarePolynomial n ell).eval joint := by
  rw [parityLiftSquarePolynomial_eval]
  positivity

theorem assignmentWeight_le_card
    {Var : Type*} [Fintype Var] (assignment : Assignment Var) :
    assignmentWeight assignment ≤ Fintype.card Var := by
  unfold assignmentWeight
  calc
    (∑ coordinate : Var, (assignment coordinate).toNat) ≤
        ∑ _coordinate : Var, 1 := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact Bool.toNat_le (assignment coordinate)
    _ = Fintype.card Var := by simp

theorem bitVec_assignmentWeight_le (n : Nat) (visible : BitVec n) :
    assignmentWeight visible ≤ n := by
  simpa using assignmentWeight_le_card visible

/-! ## Lifted support and canonical extension -/

/-- Zero set of the Hamming-weight square. -/
def parityLiftedSet (n ell : Nat) :
    Finset (Assignment (Sum (Fin n) (Fin ell))) :=
  Finset.univ.filter fun joint => parityLiftLinearValue joint = 0

theorem parityLiftedSet_nonempty (n ell : Nat) :
    (parityLiftedSet n ell).Nonempty := by
  let zero : Assignment (Sum (Fin n) (Fin ell)) := fun _ => false
  refine ⟨zero, ?_⟩
  simp [parityLiftedSet, parityLiftLinearValue, zero]

/-- Binary encoding of half the visible Hamming weight. -/
def parityLatentExtension (ell : Nat) {n : Nat}
    (visible : BitVec n) : Assignment (Fin ell) :=
  binaryAssignment ell (assignmentWeight visible / 2)

/-- Canonical lifted assignment over a visible string. -/
def parityJointExtension (ell : Nat) {n : Nat}
    (visible : BitVec n) : Assignment (Sum (Fin n) (Fin ell)) :=
  jointAssignment visible (parityLatentExtension ell visible)

theorem parityLiftedSet_mapsTo (n ell : Nat) :
    ∀ joint ∈ parityLiftedSet n ell,
      projectObs joint ∈ evenParitySupport n := by
  intro joint hJoint
  have hLinear : parityLiftLinearValue joint = 0 := by
    simpa [parityLiftedSet] using hJoint
  rw [parityLiftLinearValue_eq] at hLinear
  apply (mem_evenParitySupport_iff_even_weight _).2
  refine ⟨binaryAssignmentValue (projectLat joint), ?_⟩
  omega

theorem parityJointExtension_mem
    {n ell : Nat} (hCapacity : n < 2 ^ (ell + 1)) :
    ∀ visible ∈ evenParitySupport n,
      parityJointExtension ell visible ∈ parityLiftedSet n ell := by
  intro visible hVisible
  have hEven := (mem_evenParitySupport_iff_even_weight visible).1 hVisible
  rcases hEven with ⟨halfWeight, hWeight⟩
  have hWeightBound := bitVec_assignmentWeight_le n visible
  have hHalf : assignmentWeight visible / 2 = halfWeight := by omega
  have hHalfCapacity : halfWeight < 2 ^ ell := by
    rw [Nat.pow_succ] at hCapacity
    omega
  have hBinary :
      binaryAssignmentValue (parityLatentExtension ell visible) = halfWeight := by
    rw [parityLatentExtension, hHalf]
    exact binaryAssignmentValue_binaryAssignment_of_lt hHalfCapacity
  simp only [parityLiftedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [parityLiftLinearValue_eq]
  simp only [parityJointExtension, projectObs_jointAssignment,
    projectLat_jointAssignment, hBinary]
  omega

theorem parityJointExtension_unique
    {n ell : Nat} (hCapacity : n < 2 ^ (ell + 1)) :
    ∀ visible ∈ evenParitySupport n,
      ∀ joint ∈ parityLiftedSet n ell,
        projectObs joint = visible →
          joint = parityJointExtension ell visible := by
  intro visible hVisible joint hJoint hProject
  have hEven := (mem_evenParitySupport_iff_even_weight visible).1 hVisible
  rcases hEven with ⟨halfWeight, hWeight⟩
  have hWeightBound := bitVec_assignmentWeight_le n visible
  have hHalf : assignmentWeight visible / 2 = halfWeight := by omega
  have hHalfCapacity : halfWeight < 2 ^ ell := by
    rw [Nat.pow_succ] at hCapacity
    omega
  have hLinear : parityLiftLinearValue joint = 0 := by
    simpa [parityLiftedSet] using hJoint
  rw [parityLiftLinearValue_eq, hProject] at hLinear
  have hLatentValue : binaryAssignmentValue (projectLat joint) = halfWeight := by
    omega
  have hExtensionValue :
      binaryAssignmentValue (parityLatentExtension ell visible) = halfWeight := by
    rw [parityLatentExtension, hHalf]
    exact binaryAssignmentValue_binaryAssignment_of_lt hHalfCapacity
  have hLatent : projectLat joint = parityLatentExtension ell visible :=
    binaryAssignmentValue_injective ell (hLatentValue.trans hExtensionValue.symm)
  calc
    joint = jointAssignment (projectObs joint) (projectLat joint) :=
      (jointAssignment_projectObs_projectLat joint).symm
    _ = parityJointExtension ell visible := by
      rw [hProject, hLatent]
      rfl

theorem parityLiftedSet_uniqueExtension
    {n ell : Nat} (hCapacity : n < 2 ^ (ell + 1)) :
    ∀ visible ∈ evenParitySupport n,
      ∃! joint, joint ∈ parityLiftedSet n ell ∧
        projectObs joint = visible := by
  intro visible hVisible
  refine ⟨parityJointExtension ell visible, ?_, ?_⟩
  · exact ⟨parityJointExtension_mem hCapacity visible hVisible,
      projectObs_jointAssignment visible (parityLatentExtension ell visible)⟩
  · intro joint hJoint
    exact parityJointExtension_unique hCapacity visible hVisible
      joint hJoint.1 hJoint.2

theorem parityLiftedSet_is_groundSpace
    (n ell : Nat) (joint : Assignment (Sum (Fin n) (Fin ell))) :
    joint ∈ parityLiftedSet n ell ↔
      localEnergyEval (parityLiftSquarePolynomial n ell).toLocalEnergy joint = 0 := by
  rw [QuadraticNAND.QuadraticPolynomial.localEnergyEval_toLocalEnergy,
    parityLiftSquarePolynomial_eval]
  simp [parityLiftedSet]

theorem parityLift_isMarginalModel
    {n ell : Nat} (hCapacity : n < 2 ^ (ell + 1)) :
    IsMarginalModel (evenParityDistribution n)
      (uniformOn (parityLiftedSet n ell) (parityLiftedSet_nonempty n ell)) := by
  exact uniformOn_isMarginalModel_of_unique_extension
    (parityLiftedSet n ell) (parityLiftedSet_nonempty n ell)
    (evenParitySupport n) (evenParitySupport_nonempty n)
    (parityLiftedSet_mapsTo n ell)
    (parityLiftedSet_uniqueExtension hCapacity)

/-- If the hidden binary register can encode every half-Hamming-weight, it
gives a quadratic localization of uniform even parity. -/
theorem evenParity_has_twoLocalization_of_lt_two_pow
    {n ell : Nat} (hCapacity : n < 2 ^ (ell + 1)) :
    HasKLocalizationBits 2 ell n (evenParityDistribution n) := by
  apply hasKLocalizationBits_of_localEnergyGroundStates
    (parityLiftedSet n ell) (parityLiftedSet_nonempty n ell)
    (parityLiftSquarePolynomial n ell).toLocalEnergy
  · exact (parityLiftSquarePolynomial n ell).toLocalEnergy_respects_two
  · intro joint
    rw [QuadraticNAND.QuadraticPolynomial.localEnergyEval_toLocalEnergy]
    exact_mod_cast parityLiftSquarePolynomial_nonnegative joint
  · exact parityLiftedSet_is_groundSpace n ell
  · exact parityLift_isMarginalModel hCapacity

theorem evenParity_localizationComplexity_le_of_lt_two_pow
    {k n ell : Nat} (hk : 2 ≤ k) (hCapacity : n < 2 ^ (ell + 1)) :
    localizationComplexityBits k n (evenParityDistribution n) ≤ ell := by
  apply localizationComplexityBits_min
  exact hasKLocalizationBits_mono hk
    (evenParity_has_twoLocalization_of_lt_two_pow hCapacity)

/-- Cubic upper bound matching the uniform lower bound up to an additive
constant. -/
theorem evenParity_cubic_localizationComplexity_le_of_lt_two_pow
    {n ell : Nat} (hCapacity : n < 2 ^ (ell + 1)) :
    localizationComplexityBits 3 n (evenParityDistribution n) ≤ ell :=
  evenParity_localizationComplexity_le_of_lt_two_pow (by omega) hCapacity

/-- Whenever the lower and upper dyadic windows overlap, cubic parity
complexity is determined exactly. -/
theorem evenParity_cubic_localizationComplexity_eq_succ_of_bounds
    {n ell : Nat} (hLower : 3 * 2 ^ ell < n)
    (hUpper : n < 2 ^ (ell + 2)) :
    localizationComplexityBits 3 n (evenParityDistribution n) = ell + 1 := by
  have hComplexityLower :=
    evenParity_cubic_localizationComplexity_gt hLower
  have hExponent : ell + 2 = (ell + 1) + 1 := by omega
  rw [hExponent] at hUpper
  have hComplexityUpper :=
    evenParity_cubic_localizationComplexity_le_of_lt_two_pow
      (ell := ell + 1) hUpper
  omega

/-- An infinite explicit family with exact cubic localization complexity:
the seven-bit example is the case `ell = 1`. -/
theorem evenParity_cubic_exact_family
    {ell : Nat} (hEll : 1 ≤ ell) :
    localizationComplexityBits 3 (3 * 2 ^ ell + 1)
      (evenParityDistribution (3 * 2 ^ ell + 1)) = ell + 1 := by
  apply evenParity_cubic_localizationComplexity_eq_succ_of_bounds
  · omega
  · have hPow : 2 ≤ 2 ^ ell := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ ell := by
          gcongr
          norm_num
    have hPowerIdentity : 2 ^ (ell + 2) = 4 * 2 ^ ell := by
      rw [pow_add]
      norm_num
      ring
    rw [hPowerIdentity]
    omega

end KLocality
