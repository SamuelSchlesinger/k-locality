import KLocality.GroundStateProjection
import KLocality.NANDCircuitWithConstants

namespace KLocality
namespace NANDCircuitWithConstants

open QuadraticNAND

/-!
# Quadratic localization for NAND recognizers with hardwired constants

This module matches the paper's hardwired-input-constant convention.  Constants are
substituted into the gate polynomials and never become assignment coordinates.  A circuit
with `s` NAND gates therefore yields a 2-local lift with exactly `s` latent bits.
-/

namespace Recognizer

/-- Actual total wires, split into observed input wires and latent gate-output wires. -/
abbrev JointVar (inputCount gateCount : Nat) := Sum (Fin inputCount) (Fin gateCount)

/-- Transport the unique computed trace to the observed/latent variable split. -/
def jointTrace {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    Assignment (JointVar inputCount gateCount) :=
  fun wire => recognizer.circuit.trace input (finSumFinEquiv wire)

/-- Rename the constants-substituted recognizer Hamiltonian onto joint variables. -/
def jointHamiltonian {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    QuadraticPolynomial (JointVar inputCount gateCount) :=
  recognizer.hamiltonian.renameVars finSumFinEquiv.symm

@[simp]
theorem eval_jointHamiltonian {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount)) :
    recognizer.jointHamiltonian.eval assignment =
      recognizer.hamiltonian.eval
        (fun wire => assignment (finSumFinEquiv.symm wire)) := by
  simp [jointHamiltonian, Function.comp_def]

/-- The finite accepting ground-state set on observed and latent variables. -/
noncomputable def acceptingStates {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    Finset (Assignment (JointVar inputCount gateCount)) :=
  recognizer.jointHamiltonian.groundStates

@[simp]
theorem mem_acceptingStates_iff_zero {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount)) :
    assignment ∈ recognizer.acceptingStates ↔
      recognizer.jointHamiltonian.eval assignment = 0 := by
  simp [acceptingStates]

@[simp]
theorem projectObs_jointTrace {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    projectObs (recognizer.jointTrace input) = input := by
  funext index
  simpa [jointTrace, projectObs, Circuit.inputWire] using
    recognizer.circuit.trace_inputWire input index

/-- Restricting a transported total assignment recovers its observed part. -/
theorem inputRestriction_transport {inputCount gateCount : Nat}
    (assignment : Assignment (JointVar inputCount gateCount)) :
    Circuit.inputRestriction
        (fun wire => assignment (finSumFinEquiv.symm wire)) =
      projectObs assignment := by
  funext index
  simp only [Circuit.inputRestriction, projectObs]
  rw [Circuit.inputWire_eq_castAdd]
  simp

/-- A zero-energy joint assignment is the unique circuit trace over its visible input. -/
theorem eq_jointTrace_of_energy_zero {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount))
    (hZero : recognizer.jointHamiltonian.eval assignment = 0) :
    assignment = recognizer.jointTrace (projectObs assignment) := by
  have hTotalZero : recognizer.hamiltonian.eval
      (fun wire => assignment (finSumFinEquiv.symm wire)) = 0 := by
    simpa using hZero
  have hSatisfies : SatisfiesConstraints recognizer.circuit.constraints
      (fun wire => assignment (finSumFinEquiv.symm wire)) :=
    (recognizer.eval_hamiltonian_eq_zero_iff _).mp hTotalZero |>.1
  have hTrace := recognizer.circuit.eq_trace_inputRestriction_of_satisfies
    (fun wire => assignment (finSumFinEquiv.symm wire)) hSatisfies
  rw [inputRestriction_transport assignment] at hTrace
  funext wire
  have hAt := congrFun hTrace (finSumFinEquiv wire)
  simpa [jointTrace] using hAt

/-- Accepting ground states are exactly deterministic traces with output one. -/
theorem mem_acceptingStates_iff {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Assignment (JointVar inputCount gateCount)) :
    assignment ∈ recognizer.acceptingStates ↔
      assignment = recognizer.jointTrace (projectObs assignment) ∧
        recognizer.eval (projectObs assignment) = true := by
  rw [mem_acceptingStates_iff_zero]
  constructor
  · intro hZero
    have hTrace := eq_jointTrace_of_energy_zero recognizer assignment hZero
    refine ⟨hTrace, ?_⟩
    have hTotalZero : recognizer.hamiltonian.eval
        (fun wire => assignment (finSumFinEquiv.symm wire)) = 0 := by
      simpa using hZero
    have hOutput := (recognizer.eval_hamiltonian_eq_zero_iff _).mp hTotalZero |>.2
    have hOutput' :
        recognizer.jointTrace (projectObs assignment)
          (finSumFinEquiv.symm recognizer.output) = true := by
      rw [← hTrace]
      exact hOutput
    simpa [eval, jointTrace] using hOutput'
  · rintro ⟨hTrace, hAccepts⟩
    rw [eval_jointHamiltonian]
    apply (recognizer.eval_hamiltonian_eq_zero_iff _).mpr
    constructor
    · have hTraceSatisfies :=
        recognizer.circuit.trace_satisfies_constraints (projectObs assignment)
      have hTotalEq :
          (fun wire => assignment (finSumFinEquiv.symm wire)) =
            recognizer.circuit.trace (projectObs assignment) := by
        funext wire
        have hAt := congrFun hTrace (finSumFinEquiv.symm wire)
        simpa [jointTrace] using hAt
      rw [hTotalEq]
      exact hTraceSatisfies
    · have hOutput :
          recognizer.jointTrace (projectObs assignment)
            (finSumFinEquiv.symm recognizer.output) = true := by
        simpa [eval, jointTrace] using hAccepts
      rw [← hTrace] at hOutput
      exact hOutput

/-- The canonical trace is a ground state exactly for an accepted input. -/
theorem jointTrace_mem_acceptingStates_iff {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) (input : BitVec inputCount) :
    recognizer.jointTrace input ∈ recognizer.acceptingStates ↔
      recognizer.eval input = true := by
  rw [mem_acceptingStates_iff, projectObs_jointTrace]
  simp

/-- A recognizer of a nonempty set has a nonempty accepting ground space. -/
theorem acceptingStates_nonempty {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    recognizer.acceptingStates.Nonempty := by
  rcases hAccepted with ⟨input, hInput⟩
  refine ⟨recognizer.jointTrace input, ?_⟩
  exact (jointTrace_mem_acceptingStates_iff recognizer input).mpr
    ((hRecognizes input).mp hInput)

/-- Every accepting ground state projects into the recognized set. -/
theorem acceptingStates_mapsTo {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount))
    (hRecognizes : recognizer.Recognizes accepted) :
    ∀ assignment ∈ recognizer.acceptingStates,
      projectObs assignment ∈ accepted := by
  intro assignment hAssignment
  have hSemantics := (mem_acceptingStates_iff recognizer assignment).mp hAssignment
  exact (hRecognizes (projectObs assignment)).mpr hSemantics.2

/-- Every recognized input has exactly one accepting full trace. -/
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

/-- The uniform ground-state law projects to the uniform recognized-input law. -/
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

/-- The uniform accepting law is 2-local because its Hamiltonian is quadratic. -/
theorem acceptingUniform_isTwoLocal {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    IsKLocalMarginal 2
      (uniformOn recognizer.acceptingStates
        (acceptingStates_nonempty recognizer accepted hAccepted hRecognizes)) := by
  apply QuadraticPolynomial.uniformOn_groundStates_isTwoLocal
  intro assignment
  rw [eval_jointHamiltonian]
  exact recognizer.eval_hamiltonian_nonneg _

/-- A constants-aware `s`-gate NAND recognizer yields exactly `s` latent bits. -/
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

theorem hasTwoLocalization_of_recognizer {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) (hAccepted : accepted.Nonempty)
    (hRecognizes : recognizer.Recognizes accepted) :
    HasKLocalizationBits 2 gateCount inputCount (uniformOn accepted hAccepted) := by
  exact ⟨localizationOfRecognizer recognizer accepted hAccepted hRecognizes⟩

end Recognizer

/-- A constants-allowed sequential NAND recognizer of size `gateCount`. -/
def NANDRecognizerWitness
    (inputCount : Nat) (accepted : Finset (BitVec inputCount))
    (gateCount : Nat) : Prop :=
  ∃ recognizer : Recognizer inputCount gateCount, recognizer.Recognizes accepted

/-- Minimum gate count in the paper's hardwired-input-constant NAND convention. -/
noncomputable def CNAND
    (inputCount : Nat) (accepted : Finset (BitVec inputCount))
    (hExists : ∃ gateCount, NANDRecognizerWitness inputCount accepted gateCount) : Nat := by
  classical
  exact Nat.find hExists

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

/-- Exact constants-allowed NAND upper bound `LC₂(U_S) ≤ C_NAND(S)`. -/
theorem localizationComplexityBits_le_CNAND
    {inputCount : Nat}
    {accepted : Finset (BitVec inputCount)} (hAccepted : accepted.Nonempty)
    (hRecExists : ∃ gateCount,
      NANDRecognizerWitness inputCount accepted gateCount) :
    localizationComplexityBits 2 inputCount (uniformOn accepted hAccepted)
        (twoLocalizationExists_of_nandRecognizerExists hAccepted hRecExists) ≤
      CNAND inputCount accepted hRecExists := by
  rcases CNAND_spec inputCount accepted hRecExists with ⟨recognizer, hRecognizes⟩
  exact localizationComplexityBits_min 2 inputCount
    (uniformOn accepted hAccepted)
    (twoLocalizationExists_of_nandRecognizerExists hAccepted hRecExists)
    (CNAND inputCount accepted hRecExists)
    (Recognizer.hasTwoLocalization_of_recognizer
      recognizer accepted hAccepted hRecognizes)

end NANDCircuitWithConstants
end KLocality
