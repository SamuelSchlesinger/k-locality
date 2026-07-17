import KLocality.QuadraticNAND

namespace KLocality
namespace NANDCircuitWithConstants

open QuadraticNAND

universe u v

/-!
# Sequential NAND circuits with hardwired input constants

Hardwired constants are source syntax, not assignment coordinates.  Substituting them
directly into the quadratic NAND polynomial therefore adds no latent variables and
preserves the paper's exact gate accounting.
-/

/-- A gate source is either an actual wire or a hardwired Boolean constant. -/
inductive Source (Var : Type u) where
  | wire (var : Var)
  | constant (value : Bool)
  deriving DecidableEq

namespace Source

/-- Resolve a source against an assignment of the actual wires. -/
def eval {Var : Type u} (assignment : Var → Bool) : Source Var → Bool
  | .wire var => assignment var
  | .constant value => value

/-- Rename the actual wires occurring in a source, leaving constants unchanged. -/
def map {Var : Type u} {Var' : Type v} (mapVar : Var → Var') : Source Var → Source Var'
  | .wire var => .wire (mapVar var)
  | .constant value => .constant value

@[simp]
theorem eval_map {Var : Type u} {Var' : Type v} (mapVar : Var → Var')
    (assignment : Var' → Bool) (source : Source Var) :
    (source.map mapVar).eval assignment = source.eval (assignment ∘ mapVar) := by
  cases source <;> rfl

end Source

/-- Substitute one Boolean source into a linear monomial. -/
def linearSource {Var : Type u} (coefficient : ℤ) :
    Source Var → QuadraticPolynomial Var
  | .wire var => [.linear coefficient var]
  | .constant false => []
  | .constant true => [.constant coefficient]

@[simp]
theorem eval_linearSource {Var : Type u} (assignment : Var → Bool)
    (coefficient : ℤ) (source : Source Var) :
    QuadraticPolynomial.eval assignment (linearSource coefficient source) =
      coefficient * bitInt (source.eval assignment) := by
  cases source with
  | wire var => simp [linearSource, Source.eval, QuadraticPolynomial.eval]
  | constant value => cases value <;> simp [linearSource, Source.eval]

/-- Substitute two Boolean sources into a quadratic monomial. -/
def productSource {Var : Type u} (coefficient : ℤ) :
    Source Var → Source Var → QuadraticPolynomial Var
  | .wire left, .wire right => [.pair coefficient left right]
  | .wire _, .constant false => []
  | .wire var, .constant true => [.linear coefficient var]
  | .constant false, _ => []
  | .constant true, .wire var => [.linear coefficient var]
  | .constant true, .constant false => []
  | .constant true, .constant true => [.constant coefficient]

@[simp]
theorem eval_productSource {Var : Type u} (assignment : Var → Bool)
    (coefficient : ℤ) (left right : Source Var) :
    QuadraticPolynomial.eval assignment (productSource coefficient left right) =
      coefficient * bitInt (left.eval assignment) * bitInt (right.eval assignment) := by
  cases left with
  | wire leftVar =>
      cases right with
      | wire rightVar => simp [productSource, Source.eval, QuadraticPolynomial.eval]
      | constant value => cases value <;> simp [productSource, Source.eval]
  | constant leftValue =>
      cases leftValue <;> cases right with
      | wire rightVar => simp [productSource, Source.eval]
      | constant rightValue => cases rightValue <;> simp [productSource, Source.eval]

/-- Literal source substitution into the exact quadratic NAND polynomial. -/
def phiSources {Var : Type u} (left right output : Source Var) :
    QuadraticPolynomial Var :=
  [.constant 3] ++
    linearSource (-2) left ++
    linearSource (-2) right ++
    linearSource (-3) output ++
    productSource 1 left right ++
    productSource 2 left output ++
    productSource 2 right output

@[simp]
theorem eval_phiSources {Var : Type u} (assignment : Var → Bool)
    (left right output : Source Var) :
    QuadraticPolynomial.eval assignment (phiSources left right output) =
      phiNAND (left.eval assignment) (right.eval assignment) (output.eval assignment) := by
  simp [phiSources, phiNAND]
  ring

/-- A NAND relation whose inputs may be hardwired constants and whose output is a wire. -/
structure SourceNANDConstraint (Var : Type u) where
  left : Source Var
  right : Source Var
  output : Var

namespace SourceNANDConstraint

/-- Semantic satisfaction of a constants-aware NAND constraint. -/
def IsSatisfied {Var : Type u} (constraint : SourceNANDConstraint Var)
    (assignment : Var → Bool) : Prop :=
  assignment constraint.output =
    !(constraint.left.eval assignment && constraint.right.eval assignment)

/-- The syntactically quadratic penalty obtained by literal source substitution. -/
def polynomial {Var : Type u} (constraint : SourceNANDConstraint Var) :
    QuadraticPolynomial Var :=
  phiSources constraint.left constraint.right (.wire constraint.output)

@[simp]
theorem eval_polynomial {Var : Type u} (constraint : SourceNANDConstraint Var)
    (assignment : Var → Bool) :
    constraint.polynomial.eval assignment =
      phiNAND (constraint.left.eval assignment) (constraint.right.eval assignment)
        (assignment constraint.output) := by
  simp [polynomial, Source.eval]

theorem eval_polynomial_nonneg {Var : Type u} (constraint : SourceNANDConstraint Var)
    (assignment : Var → Bool) :
    0 ≤ constraint.polynomial.eval assignment := by
  rw [eval_polynomial]
  exact phiNAND_nonneg _ _ _

theorem eval_polynomial_eq_zero_iff {Var : Type u}
    (constraint : SourceNANDConstraint Var) (assignment : Var → Bool) :
    constraint.polynomial.eval assignment = 0 ↔ constraint.IsSatisfied assignment := by
  rw [eval_polynomial, phiNAND_eq_zero_iff]
  rfl

end SourceNANDConstraint

/-- Every constants-aware NAND constraint in a list is satisfied. -/
def SatisfiesConstraints {Var : Type u}
    (constraints : List (SourceNANDConstraint Var)) (assignment : Var → Bool) : Prop :=
  ∀ constraint ∈ constraints, constraint.IsSatisfied assignment

/-- Rename all actual wires in a constants-aware NAND constraint. -/
def mapConstraint {Var : Type u} {Var' : Type v} (mapVar : Var → Var')
    (constraint : SourceNANDConstraint Var) : SourceNANDConstraint Var' where
  left := constraint.left.map mapVar
  right := constraint.right.map mapVar
  output := mapVar constraint.output

@[simp]
theorem mapConstraint_isSatisfied_iff {Var : Type u} {Var' : Type v}
    (mapVar : Var → Var') (constraint : SourceNANDConstraint Var)
    (assignment : Var' → Bool) :
    (mapConstraint mapVar constraint).IsSatisfied assignment ↔
      constraint.IsSatisfied (assignment ∘ mapVar) := by
  simp [mapConstraint, SourceNANDConstraint.IsSatisfied, Function.comp_def]

/-- Sum the substituted quadratic penalties for a finite constraint list. -/
def constraintHamiltonian {Var : Type u} :
    List (SourceNANDConstraint Var) → QuadraticPolynomial Var
  | [] => []
  | constraint :: constraints =>
      constraint.polynomial ++ constraintHamiltonian constraints

@[simp]
theorem eval_constraintHamiltonian_nil {Var : Type u} (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment
      (constraintHamiltonian ([] : List (SourceNANDConstraint Var))) = 0 :=
  rfl

@[simp]
theorem eval_constraintHamiltonian_cons {Var : Type u}
    (constraint : SourceNANDConstraint Var)
    (constraints : List (SourceNANDConstraint Var)) (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment
        (constraintHamiltonian (constraint :: constraints)) =
      constraint.polynomial.eval assignment +
        QuadraticPolynomial.eval assignment (constraintHamiltonian constraints) := by
  simp [constraintHamiltonian]

theorem eval_constraintHamiltonian_nonneg {Var : Type u}
    (constraints : List (SourceNANDConstraint Var)) (assignment : Var → Bool) :
    0 ≤ QuadraticPolynomial.eval assignment (constraintHamiltonian constraints) := by
  induction constraints with
  | nil => simp
  | cons constraint constraints ih =>
      rw [eval_constraintHamiltonian_cons]
      exact add_nonneg (constraint.eval_polynomial_nonneg assignment) ih

theorem eval_constraintHamiltonian_eq_zero_iff {Var : Type u}
    (constraints : List (SourceNANDConstraint Var)) (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment (constraintHamiltonian constraints) = 0 ↔
      SatisfiesConstraints constraints assignment := by
  induction constraints with
  | nil => simp [SatisfiesConstraints]
  | cons constraint constraints ih =>
      rw [eval_constraintHamiltonian_cons]
      rw [add_eq_zero_iff_of_nonneg
        (constraint.eval_polynomial_nonneg assignment)
        (eval_constraintHamiltonian_nonneg constraints assignment)]
      rw [constraint.eval_polynomial_eq_zero_iff, ih]
      simp [SatisfiesConstraints]

/-- A typed sequential NAND circuit whose gate inputs may be hardwired constants. -/
inductive Circuit (inputCount : Nat) : Nat → Type where
  | nil : Circuit inputCount 0
  | snoc {gateCount : Nat} (circuit : Circuit inputCount gateCount)
      (left right : Source (Fin (inputCount + gateCount))) :
      Circuit inputCount (gateCount + 1)

namespace Circuit

/-- Embed an input index into the total actual-wire space. -/
def inputWire {inputCount gateCount : Nat} (input : Fin inputCount) :
    Fin (inputCount + gateCount) :=
  Fin.castLE (Nat.le_add_right inputCount gateCount) input

theorem inputWire_eq_castAdd {inputCount gateCount : Nat} (input : Fin inputCount) :
    inputWire (gateCount := gateCount) input = Fin.castAdd gateCount input :=
  rfl

/-- Evaluate all actual wires, resolving hardwired sources at each gate. -/
def trace {inputCount : Nat} : {gateCount : Nat} →
    Circuit inputCount gateCount → BitVec inputCount →
      Fin (inputCount + gateCount) → Bool
  | 0, .nil, input => input
  | _ + 1, .snoc circuit left right, input =>
      Fin.lastCases
        (!(left.eval (trace circuit input) && right.eval (trace circuit input)))
        (trace circuit input)

/-- Evaluate a designated actual output wire. -/
def eval {inputCount gateCount : Nat} (circuit : Circuit inputCount gateCount)
    (output : Fin (inputCount + gateCount)) (input : BitVec inputCount) : Bool :=
  circuit.trace input output

@[simp]
theorem trace_snoc_castSucc {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (left right : Source (Fin (inputCount + gateCount)))
    (wire : Fin (inputCount + gateCount)) (input : BitVec inputCount) :
    trace (.snoc circuit left right) input wire.castSucc = trace circuit input wire := by
  simp [trace]

@[simp]
theorem trace_snoc_last {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (left right : Source (Fin (inputCount + gateCount)))
    (input : BitVec inputCount) :
    trace (.snoc circuit left right) input (Fin.last (inputCount + gateCount)) =
      !(left.eval (trace circuit input) && right.eval (trace circuit input)) := by
  simp [trace]

@[simp]
theorem inputWire_succ {inputCount gateCount : Nat} (input : Fin inputCount) :
    inputWire (gateCount := gateCount + 1) input =
      (inputWire (gateCount := gateCount) input).castSucc :=
  rfl

@[simp]
theorem trace_inputWire {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (input : BitVec inputCount)
    (index : Fin inputCount) :
    trace circuit input (inputWire (gateCount := gateCount) index) = input index := by
  induction circuit with
  | nil => rfl
  | snoc circuit left right ih => simpa using ih

/-- The final gate constraint after embedding its prior-wire sources. -/
def lastConstraint {inputCount gateCount : Nat}
    (left right : Source (Fin (inputCount + gateCount))) :
    SourceNANDConstraint (Fin (inputCount + (gateCount + 1))) where
  left := left.map Fin.castSucc
  right := right.map Fin.castSucc
  output := Fin.last (inputCount + gateCount)

/-- Compile every gate into a constants-substituted NAND constraint. -/
def constraints {inputCount : Nat} : {gateCount : Nat} →
    Circuit inputCount gateCount →
      List (SourceNANDConstraint (Fin (inputCount + gateCount)))
  | 0, .nil => []
  | _ + 1, .snoc circuit left right =>
      (constraints circuit).map (mapConstraint Fin.castSucc) ++
        [lastConstraint left right]

@[simp]
theorem constraints_snoc {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (left right : Source (Fin (inputCount + gateCount))) :
    constraints (.snoc circuit left right) =
      (constraints circuit).map (mapConstraint Fin.castSucc) ++
        [lastConstraint left right] :=
  rfl

@[simp]
theorem constraints_length {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) :
    circuit.constraints.length = gateCount := by
  induction circuit with
  | nil => rfl
  | snoc circuit left right ih => simp [ih]

/-- Restrict a final total-wire assignment to the preceding actual wires. -/
def dropLast {wireCount : Nat} (assignment : Fin (wireCount + 1) → Bool) :
    Fin wireCount → Bool :=
  fun wire => assignment wire.castSucc

@[simp]
theorem dropLast_trace_snoc {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (left right : Source (Fin (inputCount + gateCount)))
    (input : BitVec inputCount) :
    dropLast (wireCount := inputCount + gateCount)
        ((Circuit.snoc circuit left right).trace input) =
      trace circuit input := by
  funext wire
  simp [dropLast]

theorem satisfies_mapConstraint_iff {Var : Type u} {Var' : Type v}
    (mapVar : Var → Var') (source : List (SourceNANDConstraint Var))
    (assignment : Var' → Bool) :
    SatisfiesConstraints (source.map (mapConstraint mapVar)) assignment ↔
      SatisfiesConstraints source (assignment ∘ mapVar) := by
  constructor
  · intro hSatisfies constraint hMember
    apply (mapConstraint_isSatisfied_iff mapVar constraint assignment).mp
    exact hSatisfies _ (List.mem_map.mpr ⟨constraint, hMember, rfl⟩)
  · intro hSatisfies mappedConstraint hMember
    rcases List.mem_map.mp hMember with ⟨constraint, hConstraint, rfl⟩
    apply (mapConstraint_isSatisfied_iff mapVar constraint assignment).mpr
    exact hSatisfies constraint hConstraint

theorem satisfies_append_singleton_iff {Var : Type u}
    (source : List (SourceNANDConstraint Var)) (last : SourceNANDConstraint Var)
    (assignment : Var → Bool) :
    SatisfiesConstraints (source ++ [last]) assignment ↔
      SatisfiesConstraints source assignment ∧ last.IsSatisfied assignment := by
  constructor
  · intro hSatisfies
    constructor
    · intro constraint hConstraint
      exact hSatisfies constraint (List.mem_append.mpr (Or.inl hConstraint))
    · exact hSatisfies last (List.mem_append.mpr (Or.inr (by simp)))
  · rintro ⟨hSource, hLast⟩ constraint hConstraint
    rcases List.mem_append.mp hConstraint with hConstraint | hConstraint
    · exact hSource constraint hConstraint
    · have hEq : constraint = last := by simpa using hConstraint
      subst constraint
      exact hLast

@[simp]
theorem satisfies_constraints_snoc_iff {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (left right : Source (Fin (inputCount + gateCount)))
    (assignment : Fin (inputCount + (gateCount + 1)) → Bool) :
    SatisfiesConstraints (constraints (.snoc circuit left right)) assignment ↔
      SatisfiesConstraints (constraints circuit) (dropLast assignment) ∧
        assignment (Fin.last (inputCount + gateCount)) =
          !(left.eval (dropLast assignment) && right.eval (dropLast assignment)) := by
  rw [constraints_snoc, satisfies_append_singleton_iff, satisfies_mapConstraint_iff]
  simp only [lastConstraint, SourceNANDConstraint.IsSatisfied, Source.eval_map]
  have hDrop : assignment ∘ Fin.castSucc = dropLast assignment := rfl
  rw [hDrop]

/-- The computed trace satisfies every compiled constants-aware constraint. -/
theorem trace_satisfies_constraints {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (input : BitVec inputCount) :
    SatisfiesConstraints circuit.constraints (circuit.trace input) := by
  induction circuit with
  | nil => simp [SatisfiesConstraints, constraints]
  | snoc circuit left right ih =>
      rw [satisfies_constraints_snoc_iff]
      rw [dropLast_trace_snoc]
      exact ⟨ih, trace_snoc_last circuit left right input⟩

/-- Agreement of a total assignment with fixed external inputs. -/
def AgreesOnInputs {inputCount gateCount : Nat}
    (assignment : Fin (inputCount + gateCount) → Bool)
    (input : BitVec inputCount) : Prop :=
  ∀ index, assignment (inputWire (gateCount := gateCount) index) = input index

/-- Restrict an actual-wire assignment to its external input wires. -/
def inputRestriction {inputCount gateCount : Nat}
    (assignment : Fin (inputCount + gateCount) → Bool) : BitVec inputCount :=
  fun index => assignment (inputWire (gateCount := gateCount) index)

@[simp]
theorem agreesOnInputs_inputRestriction {inputCount gateCount : Nat}
    (assignment : Fin (inputCount + gateCount) → Bool) :
    AgreesOnInputs assignment (inputRestriction assignment) := by
  intro index
  rfl

/-- A satisfying assignment extending fixed inputs is the unique computed trace. -/
theorem eq_trace_of_satisfies_of_agrees {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (input : BitVec inputCount)
    (assignment : Fin (inputCount + gateCount) → Bool)
    (hSatisfies : SatisfiesConstraints circuit.constraints assignment)
    (hInputs : AgreesOnInputs assignment input) :
    assignment = circuit.trace input := by
  induction circuit with
  | nil =>
      funext index
      simpa [AgreesOnInputs, inputWire] using hInputs index
  | @snoc gateCount circuit left right ih =>
      rw [satisfies_constraints_snoc_iff] at hSatisfies
      rcases hSatisfies with ⟨hPrevious, hLast⟩
      have hPreviousInputs : AgreesOnInputs (dropLast assignment) input := by
        intro index
        simpa [AgreesOnInputs, dropLast] using hInputs index
      have hPreviousTrace : dropLast assignment = circuit.trace input :=
        ih (dropLast assignment) hPrevious hPreviousInputs
      funext wire
      refine Fin.lastCases ?_ (fun previousWire => ?_) wire
      · calc
          assignment (Fin.last (inputCount + gateCount)) =
              !(left.eval (dropLast assignment) &&
                right.eval (dropLast assignment)) := hLast
          _ = !(left.eval (circuit.trace input) &&
                right.eval (circuit.trace input)) := by rw [hPreviousTrace]
          _ = trace (.snoc circuit left right) input
              (Fin.last (inputCount + gateCount)) := by rw [trace_snoc_last]
      · simpa [dropLast] using congrFun hPreviousTrace previousWire

/-- Every satisfying assignment is the trace over its own external inputs. -/
theorem eq_trace_inputRestriction_of_satisfies {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (assignment : Fin (inputCount + gateCount) → Bool)
    (hSatisfies : SatisfiesConstraints circuit.constraints assignment) :
    assignment = circuit.trace (inputRestriction assignment) :=
  eq_trace_of_satisfies_of_agrees circuit (inputRestriction assignment) assignment
    hSatisfies (agreesOnInputs_inputRestriction assignment)

/-- The complete quadratic Hamiltonian for all gates of a circuit. -/
def hamiltonian {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) :
    QuadraticPolynomial (Fin (inputCount + gateCount)) :=
  constraintHamiltonian circuit.constraints

theorem eval_hamiltonian_nonneg {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (assignment : Fin (inputCount + gateCount) → Bool) :
    0 ≤ circuit.hamiltonian.eval assignment :=
  eval_constraintHamiltonian_nonneg circuit.constraints assignment

theorem eval_hamiltonian_eq_zero_iff {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (assignment : Fin (inputCount + gateCount) → Bool) :
    circuit.hamiltonian.eval assignment = 0 ↔
      SatisfiesConstraints circuit.constraints assignment :=
  eval_constraintHamiltonian_eq_zero_iff circuit.constraints assignment

end Circuit

/-- A constants-aware sequential NAND circuit with a designated actual output wire. -/
structure Recognizer (inputCount gateCount : Nat) where
  circuit : Circuit inputCount gateCount
  output : Fin (inputCount + gateCount)

namespace Recognizer

/-- Evaluate the designated output. -/
def eval {inputCount gateCount : Nat} (recognizer : Recognizer inputCount gateCount)
    (input : BitVec inputCount) : Bool :=
  recognizer.circuit.eval recognizer.output input

/-- Recognition of a finite set of visible inputs. -/
def Recognizes {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (accepted : Finset (BitVec inputCount)) : Prop :=
  ∀ input, input ∈ accepted ↔ recognizer.eval input = true

/-- Gate penalties plus the linear designated-output-one penalty. -/
def hamiltonian {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount) :
    QuadraticPolynomial (Fin (inputCount + gateCount)) :=
  recognizer.circuit.hamiltonian ++ outputOnePenalty recognizer.output

@[simp]
theorem eval_hamiltonian {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Fin (inputCount + gateCount) → Bool) :
    recognizer.hamiltonian.eval assignment =
      recognizer.circuit.hamiltonian.eval assignment +
        QuadraticPolynomial.eval assignment (outputOnePenalty recognizer.output) := by
  simp [hamiltonian]

theorem eval_hamiltonian_nonneg {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Fin (inputCount + gateCount) → Bool) :
    0 ≤ recognizer.hamiltonian.eval assignment := by
  rw [eval_hamiltonian]
  exact add_nonneg (recognizer.circuit.eval_hamiltonian_nonneg assignment)
    (eval_outputOnePenalty_nonneg assignment recognizer.output)

/-- Zero recognizer energy means a valid gate trace whose designated output is one. -/
theorem eval_hamiltonian_eq_zero_iff {inputCount gateCount : Nat}
    (recognizer : Recognizer inputCount gateCount)
    (assignment : Fin (inputCount + gateCount) → Bool) :
    recognizer.hamiltonian.eval assignment = 0 ↔
      SatisfiesConstraints recognizer.circuit.constraints assignment ∧
        assignment recognizer.output = true := by
  rw [eval_hamiltonian]
  rw [add_eq_zero_iff_of_nonneg
    (recognizer.circuit.eval_hamiltonian_nonneg assignment)
    (eval_outputOnePenalty_nonneg assignment recognizer.output)]
  rw [recognizer.circuit.eval_hamiltonian_eq_zero_iff,
    eval_outputOnePenalty_eq_zero_iff]

end Recognizer

end NANDCircuitWithConstants
end KLocality
