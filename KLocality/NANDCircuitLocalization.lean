import KLocality.GroundStateProjection
import KLocality.NANDCircuit

namespace KLocality
namespace NANDCircuit

open QuadraticNAND

/-!
# Quadratic localization from sequential NAND recognizers

This module combines the typed sequential circuit semantics with the quadratic NAND
Hamiltonian.  The key point is trace uniqueness: every accepted input has exactly one
accepting full wire assignment.  Consequently, the uniform law on accepting ground states
projects to the uniform law on accepted inputs, with no witness-multiplicity distortion.

The circuit model in this module is constant-free.  Hardwired constants from the paper's
stated NAND convention require a separate compilation theorem.
-/

/-- A sequential NAND circuit together with a designated output wire. -/
structure Recognizer (inputCount gateCount : Nat) where
  circuit : Circuit inputCount gateCount
  output : Fin (inputCount + gateCount)

namespace Recognizer

/-- Evaluate the designated output wire. -/
def eval {inputCount gateCount : Nat} (recognizer : Recognizer inputCount gateCount)
    (input : BitVec inputCount) : Bool :=
  recognizer.circuit.eval recognizer.output input

/-- A recognizer accepts exactly the members of a finite input set. -/
def Recognizes {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) : Prop :=
  ∀ input, input ∈ accepted ↔ recognizer.eval input = true

/-- View the total wire type as observed input wires plus latent gate wires. -/
abbrev JointVar (inputCount gateCount : Nat) := Sum (Fin inputCount) (Fin gateCount)

/-- Transport a computed total-wire trace to the observed/latent variable split. -/
def jointTrace {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    Assignment (JointVar inputCount gateCount) :=
  fun wire => recognizer.circuit.trace input (finSumFinEquiv wire)

/-- Transport the compiled gate constraints to the observed/latent variable split. -/
def jointConstraints {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    List (NANDConstraint (JointVar inputCount gateCount)) :=
  recognizer.circuit.constraints.map
    (Circuit.mapConstraint finSumFinEquiv.symm)

/-- The designated output in the observed/latent variable split. -/
def jointOutput {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    JointVar inputCount gateCount :=
  finSumFinEquiv.symm recognizer.output

/-- Inputs accepted by the designated output wire. -/
def acceptedInputs {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) : Finset (BitVec inputCount) :=
  Finset.univ.filter fun input => recognizer.eval input = true

@[simp]
theorem mem_acceptedInputs_iff {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    input ∈ recognizer.acceptedInputs ↔ recognizer.eval input = true := by
  simp [acceptedInputs]

/-- The accepting ground states of the compiled recognizer Hamiltonian. -/
def acceptingStates {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    Finset (Assignment (JointVar inputCount gateCount)) :=
  nandAcceptingGroundStates recognizer.jointConstraints recognizer.jointOutput

@[simp]
theorem projectObs_jointTrace {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    projectObs (recognizer.jointTrace input) = input := by
  funext index
  simpa [jointTrace, projectObs, Circuit.inputWire] using
    recognizer.circuit.trace_inputWire input index

/-- Satisfaction of transported constraints is satisfaction on the original total wires. -/
theorem satisfies_jointConstraints_iff {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount)) :
    SatisfiesNANDConstraints recognizer.jointConstraints assignment ↔
      SatisfiesNANDConstraints recognizer.circuit.constraints
        (fun wire => assignment (finSumFinEquiv.symm wire)) := by
  exact Circuit.satisfies_mapConstraint_iff finSumFinEquiv.symm
    recognizer.circuit.constraints assignment

/-- A transported computed trace satisfies every transported gate constraint. -/
theorem jointTrace_satisfies_constraints {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    SatisfiesNANDConstraints recognizer.jointConstraints
      (recognizer.jointTrace input) := by
  rw [satisfies_jointConstraints_iff]
  simpa [jointTrace, Function.comp_def] using
    recognizer.circuit.trace_satisfies_constraints input

/-- Restricting a joint assignment through total-wire names recovers its observed part. -/
theorem inputRestriction_transport {inputCount gateCount : Nat}
    (assignment : Assignment (JointVar inputCount gateCount)) :
    Circuit.inputRestriction
        (fun wire => assignment (finSumFinEquiv.symm wire)) =
      projectObs assignment := by
  funext index
  simp only [Circuit.inputRestriction, projectObs]
  rw [Circuit.inputWire_eq_castAdd]
  simp

/-- Every satisfying transported assignment is the unique trace over its observed input. -/
theorem eq_jointTrace_of_satisfies {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount))
    (hSatisfies : SatisfiesNANDConstraints recognizer.jointConstraints assignment) :
    assignment = recognizer.jointTrace (projectObs assignment) := by
  have hTotal : SatisfiesNANDConstraints recognizer.circuit.constraints
      (fun wire => assignment (finSumFinEquiv.symm wire)) :=
    (satisfies_jointConstraints_iff recognizer assignment).mp hSatisfies
  have hTrace := recognizer.circuit.eq_trace_inputRestriction_of_satisfies
    (fun wire => assignment (finSumFinEquiv.symm wire)) hTotal
  rw [inputRestriction_transport assignment] at hTrace
  funext wire
  have hAt := congrFun hTrace (finSumFinEquiv wire)
  simpa [jointTrace] using hAt

/-- Accepting-state membership has exact deterministic-trace semantics. -/
theorem mem_acceptingStates_iff {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount)) :
    assignment ∈ recognizer.acceptingStates ↔
      assignment = recognizer.jointTrace (projectObs assignment) ∧
        recognizer.eval (projectObs assignment) = true := by
  rw [acceptingStates, mem_nandAcceptingGroundStates_iff_satisfies]
  constructor
  · rintro ⟨hSatisfies, hOutput⟩
    have hTrace := eq_jointTrace_of_satisfies recognizer assignment hSatisfies
    refine ⟨hTrace, ?_⟩
    have hOutput' :
        recognizer.jointTrace (projectObs assignment) recognizer.jointOutput = true := by
      rw [← hTrace]
      exact hOutput
    simpa [eval, jointTrace, jointOutput] using hOutput'
  · rintro ⟨hTrace, hAccepts⟩
    constructor
    · rw [hTrace]
      exact jointTrace_satisfies_constraints recognizer _
    · calc
        assignment recognizer.jointOutput =
            recognizer.jointTrace (projectObs assignment) recognizer.jointOutput :=
          congrFun hTrace recognizer.jointOutput
        _ = recognizer.eval (projectObs assignment) := by
          simp [eval, jointTrace, jointOutput]
        _ = true := hAccepts

/-- The canonical trace is accepting exactly when the recognizer accepts its input. -/
theorem jointTrace_mem_acceptingStates_iff {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    recognizer.jointTrace input ∈ recognizer.acceptingStates ↔
      recognizer.eval input = true := by
  rw [mem_acceptingStates_iff, projectObs_jointTrace]
  simp

/-- A recognizer for a nonempty set has a nonempty accepting ground space. -/
theorem acceptingStates_nonempty {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    recognizer.acceptingStates.Nonempty := by
  rcases hAccepted with ⟨input, hInput⟩
  refine ⟨recognizer.jointTrace input, ?_⟩
  exact (jointTrace_mem_acceptingStates_iff recognizer input).mpr
    ((hRecognizes input).mp hInput)

/-- Every accepting full state projects into the recognized input set. -/
theorem acceptingStates_mapsTo {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount))
    (hRecognizes : recognizer.Recognizes accepted) :
    ∀ assignment ∈ recognizer.acceptingStates,
      projectObs assignment ∈ accepted := by
  intro assignment hAssignment
  have hSemantics := (mem_acceptingStates_iff recognizer assignment).mp hAssignment
  exact (hRecognizes (projectObs assignment)).mpr hSemantics.2

/-- Every recognized input has exactly one accepting full wire assignment. -/
theorem acceptingStates_unique_extension {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount))
    (hRecognizes : recognizer.Recognizes accepted) :
    ∀ input ∈ accepted, ∃! assignment,
      assignment ∈ recognizer.acceptingStates ∧ projectObs assignment = input := by
  intro input hInput
  refine ⟨recognizer.jointTrace input, ?_, ?_⟩
  · exact ⟨(jointTrace_mem_acceptingStates_iff recognizer input).mpr
      ((hRecognizes input).mp hInput), projectObs_jointTrace recognizer input⟩
  · intro assignment hAssignment
    have hSemantics :=
      (mem_acceptingStates_iff recognizer assignment).mp hAssignment.1
    calc
      assignment = recognizer.jointTrace (projectObs assignment) := hSemantics.1
      _ = recognizer.jointTrace input := by rw [hAssignment.2]

/-- The uniform accepting ground-state law projects to the uniform accepted-input law. -/
theorem acceptingUniform_isMarginalModel {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    IsMarginalModel (uniformOn accepted hAccepted)
      (uniformOn recognizer.acceptingStates
        (acceptingStates_nonempty recognizer accepted hAccepted hRecognizes)) := by
  apply uniformOn_isMarginalModel_of_unique_extension
  · exact acceptingStates_mapsTo recognizer accepted hRecognizes
  · exact acceptingStates_unique_extension recognizer accepted hRecognizes

/-- The uniform accepting ground-state law is 2-local. -/
theorem acceptingUniform_isTwoLocal {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    IsKLocalMarginal 2
      (uniformOn recognizer.acceptingStates
        (acceptingStates_nonempty recognizer accepted hAccepted hRecognizes)) := by
  simpa [acceptingStates] using
    (uniformOn_nandAcceptingGroundStates_isTwoLocal
      recognizer.jointConstraints recognizer.jointOutput
      (acceptingStates_nonempty recognizer accepted hAccepted hRecognizes))

/-- A constant-free sequential NAND recognizer yields one latent bit per gate. -/
noncomputable def localizationOfRecognizer {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    KLocalization 2 (Fin inputCount) (Fin gateCount) (uniformOn accepted hAccepted) :=
  { lifted := uniformOn recognizer.acceptingStates
      (acceptingStates_nonempty recognizer accepted hAccepted hRecognizes)
    marginal := acceptingUniform_isMarginalModel
      recognizer accepted hAccepted hRecognizes
    kLocal := acceptingUniform_isTwoLocal
      recognizer accepted hAccepted hRecognizes }

/-- Existence form of `localizationOfRecognizer`. -/
theorem hasTwoLocalization_of_recognizer {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    HasKLocalizationBits 2 gateCount inputCount (uniformOn accepted hAccepted) := by
  exact ⟨localizationOfRecognizer recognizer accepted hAccepted hRecognizes⟩

end Recognizer

/-- A constant-free sequential NAND recognizer of size `gateCount`. -/
def NANDRecognizerWitness
    (inputCount : Nat) (accepted : Finset (BitVec inputCount))
    (gateCount : Nat) : Prop :=
  ∃ recognizer : Recognizer inputCount gateCount, recognizer.Recognizes accepted

/-- Minimum gate count in the constant-free sequential NAND model. -/
noncomputable def CNAND
    (inputCount : Nat) (accepted : Finset (BitVec inputCount))
    (hExists : ∃ gateCount, NANDRecognizerWitness inputCount accepted gateCount) : Nat := by
  classical
  exact Nat.find hExists

/-- Paper-shaped notation for the constant-free sequential NAND complexity. -/
noncomputable abbrev C_NAND
    (inputCount : Nat) (accepted : Finset (BitVec inputCount))
    (hExists : ∃ gateCount, NANDRecognizerWitness inputCount accepted gateCount) : Nat :=
  CNAND inputCount accepted hExists

theorem CNAND_spec
    (inputCount : Nat) (accepted : Finset (BitVec inputCount))
    (hExists : ∃ gateCount, NANDRecognizerWitness inputCount accepted gateCount) :
    NANDRecognizerWitness inputCount accepted (CNAND inputCount accepted hExists) := by
  classical
  exact Nat.find_spec hExists

theorem CNAND_min
    (inputCount : Nat) (accepted : Finset (BitVec inputCount))
    (hExists : ∃ gateCount, NANDRecognizerWitness inputCount accepted gateCount) :
    ∀ gateCount, NANDRecognizerWitness inputCount accepted gateCount →
      CNAND inputCount accepted hExists ≤ gateCount := by
  classical
  intro gateCount hWitness
  exact Nat.find_min' hExists hWitness

/-- A given constant-free NAND recognizer bounds 2-localization complexity by its gate count. -/
theorem localizationComplexityBits_le_of_nandRecognizer
    {inputCount gateCount : Nat}
    {accepted : Finset (BitVec inputCount)} (hAccepted : accepted.Nonempty)
    (recognizer : Recognizer inputCount gateCount)
    (hRecognizes : recognizer.Recognizes accepted) :
    localizationComplexityBits 2 inputCount (uniformOn accepted hAccepted) ≤
      gateCount := by
  exact localizationComplexityBits_min 2 inputCount
    (uniformOn accepted hAccepted) gateCount
      (Recognizer.hasTwoLocalization_of_recognizer
        recognizer accepted hAccepted hRecognizes)

/-- Any recognizer-existence witness supplies existence of a 2-localization. -/
theorem twoLocalizationExists_of_nandRecognizerExists
    {inputCount : Nat}
    {accepted : Finset (BitVec inputCount)} (hAccepted : accepted.Nonempty)
    (hRecExists : ∃ gateCount,
      NANDRecognizerWitness inputCount accepted gateCount) :
    ∃ latentBits,
      HasKLocalizationBits 2 latentBits inputCount (uniformOn accepted hAccepted) := by
  rcases hRecExists with ⟨gateCount, recognizer, hRecognizes⟩
  exact ⟨gateCount, Recognizer.hasTwoLocalization_of_recognizer
    recognizer accepted hAccepted hRecognizes⟩

/-- Checked constant-free NAND upper bound `LC₂(U_S) ≤ C_NAND(S)`. -/
theorem localizationComplexityBits_le_CNAND
    {inputCount : Nat}
    {accepted : Finset (BitVec inputCount)} (hAccepted : accepted.Nonempty)
    (hRecExists : ∃ gateCount,
      NANDRecognizerWitness inputCount accepted gateCount) :
    localizationComplexityBits 2 inputCount (uniformOn accepted hAccepted) ≤
      CNAND inputCount accepted hRecExists := by
  rcases CNAND_spec inputCount accepted hRecExists with ⟨recognizer, hRecognizes⟩
  exact localizationComplexityBits_le_of_nandRecognizer
    hAccepted recognizer hRecognizes

end NANDCircuit
end KLocality
