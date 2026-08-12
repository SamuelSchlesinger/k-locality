import KLocality.BooleanTilt
import KLocality.NANDCircuitLocalization
import KLocality.QuadraticFeaturePolynomial

namespace KLocality
namespace NANDCircuit

open QuadraticNAND

/-!
# Full-support Boolean tilts from NAND circuits

If a sequential NAND circuit computes a Boolean function `f`, put the
Boolean tilt `D_f` on its inputs and push that law onto the circuit's unique
wire trace.  The trace support is cut out by the quadratic NAND Hamiltonian,
and the log-density on that support is a unary function of the output wire.
Thus a size-`s` circuit gives a 2-localization of `D_f` with exactly `s`
latent bits.
-/

namespace Recognizer

/-- Push the full-support Boolean tilt onto the unique full wire trace. -/
noncomputable def booleanTiltLifted
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    Distribution (Assignment (JointVar inputCount gateCount)) :=
  (booleanTiltDistribution recognizer.eval).map recognizer.jointTrace

/-- Projection of the trace lift recovers the Boolean tilt. -/
theorem booleanTiltLifted_isMarginalModel
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    IsMarginalModel (booleanTiltDistribution recognizer.eval)
      recognizer.booleanTiltLifted := by
  unfold IsMarginalModel booleanTiltLifted
  rw [PMF.map_comp]
  have hProjection : projectObs ∘ recognizer.jointTrace = id := by
    funext input
    exact recognizer.projectObs_jointTrace input
  rw [hProjection, PMF.map_id]

/-- A circuit trace is injective because it retains every input wire. -/
theorem jointTrace_injective
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    Function.Injective recognizer.jointTrace := by
  intro left right hTrace
  have hProjected := congrArg projectObs hTrace
  simpa using hProjected

/-- The pushed-forward tilt has exactly the circuit-trace graph as support. -/
theorem booleanTiltLifted_support
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    recognizer.booleanTiltLifted.support = Set.range recognizer.jointTrace := by
  rw [booleanTiltLifted, PMF.support_map, booleanTiltDistribution_support]
  exact Set.image_univ

/-- Support membership is equivalent to satisfying all compiled NAND gates. -/
theorem mem_booleanTiltLifted_support_iff_satisfies
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount)) :
    assignment ∈ recognizer.booleanTiltLifted.support ↔
      SatisfiesNANDConstraints recognizer.jointConstraints assignment := by
  rw [booleanTiltLifted_support]
  constructor
  · rintro ⟨input, rfl⟩
    exact recognizer.jointTrace_satisfies_constraints input
  · intro hSatisfies
    exact ⟨projectObs assignment,
      (recognizer.eq_jointTrace_of_satisfies assignment hSatisfies).symm⟩

/-- Injectivity of the trace means no probability is distorted by the lift. -/
@[simp]
theorem booleanTiltLifted_apply_jointTrace
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    recognizer.booleanTiltLifted (recognizer.jointTrace input) =
      booleanTiltDistribution recognizer.eval input := by
  rw [booleanTiltLifted, PMF.map_apply]
  rw [tsum_eq_single input]
  · simp
  · intro other hOther
    have hTraceNe : recognizer.jointTrace input ≠ recognizer.jointTrace other := by
      intro hTrace
      exact hOther (recognizer.jointTrace_injective hTrace).symm
    simp [hTraceNe]

/-- The canonical order-two polynomial exposing the valid trace graph. -/
noncomputable def booleanTiltEnergy
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    FeaturePolynomial (JointVar inputCount gateCount) 2 :=
  (nandHamiltonian recognizer.jointConstraints).toFeaturePolynomial

@[simp]
theorem booleanTiltEnergy_eval
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount)) :
    recognizer.booleanTiltEnergy.eval assignment =
      ((nandHamiltonian recognizer.jointConstraints).eval assignment : ℝ) := by
  simp [booleanTiltEnergy]

/-- The circuit-trace graph is an exposed face of the order-two feature
polytope. -/
theorem booleanTiltLifted_isFacialSupport
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    IsFacialSupport 2 recognizer.booleanTiltLifted.support := by
  refine ⟨recognizer.booleanTiltEnergy, ?_, ?_⟩
  · intro assignment
    rw [booleanTiltEnergy_eval]
    exact_mod_cast eval_nandHamiltonian_nonneg
      recognizer.jointConstraints assignment
  · intro assignment
    rw [booleanTiltEnergy_eval]
    norm_cast
    rw [eval_nandHamiltonian_eq_zero_iff]
    exact (recognizer.mem_booleanTiltLifted_support_iff_satisfies assignment).symm

/-- The singleton feature containing the designated output wire. -/
def booleanTiltOutputScope
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    FeatureScope (JointVar inputCount gateCount) 2 :=
  ⟨{recognizer.jointOutput}, by simp⟩

@[simp]
theorem monomialValue_singleton
    {Var : Type*} [Fintype Var] [DecidableEq Var]
    (coordinate : Var) (assignment : Assignment Var) :
    monomialValue {coordinate} assignment =
      if assignment coordinate then 1 else 0 := by
  cases hVariable : assignment coordinate <;>
    simp [monomialValue, hVariable]

@[simp]
theorem jointTrace_jointOutput
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    recognizer.jointTrace input recognizer.jointOutput = recognizer.eval input := by
  simp [jointTrace, jointOutput, eval]

/-- On the trace graph, the log-density consists of a constant plus a unary
output-wire potential. -/
noncomputable def booleanTiltLogPotential
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    FeaturePolynomial (JointVar inputCount gateCount) 2 :=
  FeaturePolynomial.constant 2
      (Real.log (booleanTiltLowWeight recognizer.eval)) +
    FeaturePolynomial.single recognizer.booleanTiltOutputScope
      (Real.log (booleanTiltHighWeight recognizer.eval) -
        Real.log (booleanTiltLowWeight recognizer.eval))

@[simp]
theorem booleanTiltLogPotential_eval_jointTrace
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    recognizer.booleanTiltLogPotential.eval (recognizer.jointTrace input) =
      if recognizer.eval input then
        Real.log (booleanTiltHighWeight recognizer.eval)
      else Real.log (booleanTiltLowWeight recognizer.eval) := by
  rw [booleanTiltLogPotential, FeaturePolynomial.eval_add,
    FeaturePolynomial.eval_constant, FeaturePolynomial.eval_single]
  change Real.log (booleanTiltLowWeight recognizer.eval) +
      (Real.log (booleanTiltHighWeight recognizer.eval) -
        Real.log (booleanTiltLowWeight recognizer.eval)) *
          monomialValue {recognizer.jointOutput} (recognizer.jointTrace input) = _
  rw [monomialValue_singleton, jointTrace_jointOutput]
  cases hOutput : recognizer.eval input <;> simp

/-- The trace lift has an order-two log-density on its positive support. -/
theorem booleanTiltLifted_isFeatureGibbs
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    IsFeatureGibbs 2 recognizer.booleanTiltLifted := by
  refine ⟨recognizer.booleanTiltLogPotential, ?_⟩
  intro assignment hSupport
  rw [booleanTiltLifted_support] at hSupport
  rcases hSupport with ⟨input, rfl⟩
  rw [booleanTiltLifted_apply_jointTrace,
    booleanTiltDistribution_apply_toReal,
    booleanTiltLogPotential_eval_jointTrace]
  cases hOutput : recognizer.eval input with
  | false =>
      rw [booleanTiltWeights_of_false hOutput]
      simp
  | true =>
      rw [booleanTiltWeights_of_true hOutput]
      simp

/-- The lifted Boolean tilt is face--Gibbs at order two. -/
theorem booleanTiltLifted_isFaceGibbs
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    IsFaceGibbs 2 recognizer.booleanTiltLifted :=
  ⟨recognizer.booleanTiltLifted_isFacialSupport,
    recognizer.booleanTiltLifted_isFeatureGibbs⟩

/-- The lifted Boolean tilt is an order-two local marginal model. -/
theorem booleanTiltLifted_isTwoLocal
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    IsKLocalMarginal 2 recognizer.booleanTiltLifted :=
  isKLocalMarginal_of_isFaceGibbs 2 recognizer.booleanTiltLifted
    recognizer.booleanTiltLifted_isFaceGibbs

/-- A size-`s` NAND circuit gives a 2-localization of its Boolean tilt using
exactly its `s` gate wires as latent variables. -/
noncomputable def booleanTiltLocalization
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    KLocalization 2 (Fin inputCount) (Fin gateCount)
      (booleanTiltDistribution recognizer.eval) where
  lifted := recognizer.booleanTiltLifted
  marginal := recognizer.booleanTiltLifted_isMarginalModel
  kLocal := recognizer.booleanTiltLifted_isTwoLocal

theorem hasTwoLocalization_booleanTilt
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    HasKLocalizationBits 2 gateCount inputCount
      (booleanTiltDistribution recognizer.eval) :=
  ⟨recognizer.booleanTiltLocalization⟩

theorem hasThreeLocalization_booleanTilt
    {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    HasKLocalizationBits 3 gateCount inputCount
      (booleanTiltDistribution recognizer.eval) :=
  hasKLocalizationBits_mono (by norm_num)
    recognizer.hasTwoLocalization_booleanTilt

theorem hasTwoLocalization_booleanTilt_of_computes
    {inputCount gateCount : Nat} {f : BitVec inputCount → Bool}
    (recognizer : Recognizer inputCount gateCount)
    (hComputes : recognizer.eval = f) :
    HasKLocalizationBits 2 gateCount inputCount
      (booleanTiltDistribution f) := by
  simpa [hComputes] using recognizer.hasTwoLocalization_booleanTilt

theorem hasThreeLocalization_booleanTilt_of_computes
    {inputCount gateCount : Nat} {f : BitVec inputCount → Bool}
    (recognizer : Recognizer inputCount gateCount)
    (hComputes : recognizer.eval = f) :
    HasKLocalizationBits 3 gateCount inputCount
      (booleanTiltDistribution f) :=
  hasKLocalizationBits_mono (by norm_num)
    (recognizer.hasTwoLocalization_booleanTilt_of_computes hComputes)

theorem localizationComplexityBits_two_booleanTilt_le
    {inputCount gateCount : Nat} {f : BitVec inputCount → Bool}
    (recognizer : Recognizer inputCount gateCount)
    (hComputes : recognizer.eval = f) :
    localizationComplexityBits 2 inputCount (booleanTiltDistribution f) ≤
      gateCount :=
  localizationComplexityBits_min 2 inputCount (booleanTiltDistribution f)
    gateCount (recognizer.hasTwoLocalization_booleanTilt_of_computes hComputes)

theorem localizationComplexityBits_three_booleanTilt_le
    {inputCount gateCount : Nat} {f : BitVec inputCount → Bool}
    (recognizer : Recognizer inputCount gateCount)
    (hComputes : recognizer.eval = f) :
    localizationComplexityBits 3 inputCount (booleanTiltDistribution f) ≤
      gateCount :=
  localizationComplexityBits_min 3 inputCount (booleanTiltDistribution f)
    gateCount (recognizer.hasThreeLocalization_booleanTilt_of_computes hComputes)

end Recognizer

/-- The finite set on which a Boolean function is true. -/
def booleanTrueInputs
    {inputCount : Nat} (f : BitVec inputCount → Bool) :
    Finset (BitVec inputCount) :=
  Finset.univ.filter fun input => f input = true

@[simp]
theorem mem_booleanTrueInputs_iff
    {inputCount : Nat} (f : BitVec inputCount → Bool)
    (input : BitVec inputCount) :
    input ∈ booleanTrueInputs f ↔ f input = true := by
  simp [booleanTrueInputs]

/-- Recognizing the true set is equivalent to computing the Boolean
function. -/
theorem Recognizer.eval_eq_of_recognizes_booleanTrueInputs
    {inputCount gateCount : Nat} {f : BitVec inputCount → Bool}
    (recognizer : Recognizer inputCount gateCount)
    (hRecognizes : recognizer.Recognizes (booleanTrueInputs f)) :
    recognizer.eval = f := by
  funext input
  have hAtInput := hRecognizes input
  cases hFunction : f input <;> cases hCircuit : recognizer.eval input <;>
    simp_all [booleanTrueInputs]

/-- Exact bridge from constant-free NAND complexity to localization
complexity for the full-support rational Boolean tilt. -/
theorem localizationComplexityBits_three_booleanTilt_le_CNAND
    {inputCount : Nat} (f : BitVec inputCount → Bool)
    (hExists : ∃ gateCount,
      NANDRecognizerWitness inputCount (booleanTrueInputs f) gateCount) :
    localizationComplexityBits 3 inputCount (booleanTiltDistribution f) ≤
      CNAND inputCount (booleanTrueInputs f) hExists := by
  rcases CNAND_spec inputCount (booleanTrueInputs f) hExists with
    ⟨recognizer, hRecognizes⟩
  exact recognizer.localizationComplexityBits_three_booleanTilt_le
    (recognizer.eval_eq_of_recognizes_booleanTrueInputs hRecognizes)

/-- The same exact bridge already holds at locality two. -/
theorem localizationComplexityBits_two_booleanTilt_le_CNAND
    {inputCount : Nat} (f : BitVec inputCount → Bool)
    (hExists : ∃ gateCount,
      NANDRecognizerWitness inputCount (booleanTrueInputs f) gateCount) :
    localizationComplexityBits 2 inputCount (booleanTiltDistribution f) ≤
      CNAND inputCount (booleanTrueInputs f) hExists := by
  rcases CNAND_spec inputCount (booleanTrueInputs f) hExists with
    ⟨recognizer, hRecognizes⟩
  exact recognizer.localizationComplexityBits_two_booleanTilt_le
    (recognizer.eval_eq_of_recognizes_booleanTrueInputs hRecognizes)

end NANDCircuit
end KLocality
