import KLocality.QuadraticNAND

namespace KLocality
namespace NANDCircuit

open QuadraticNAND

/-!
# Sequential acyclic NAND circuits

The gate-count index records how many sequential gate wires have been introduced.
In `snoc circuit left right`, both inputs lie among the original input wires and the
already constructed gate wires.  Consequently, acyclicity is enforced by the type.
-/

/-- A NAND circuit with `inputCount` inputs and `gateCount` sequential gates. -/
inductive Circuit (inputCount : Nat) : Nat → Type where
  | nil : Circuit inputCount 0
  | snoc {gateCount : Nat} (circuit : Circuit inputCount gateCount)
      (left right : Fin (inputCount + gateCount)) : Circuit inputCount (gateCount + 1)

namespace Circuit

/-- Embed an input index into the total wire space. -/
def inputWire {inputCount gateCount : Nat} (input : Fin inputCount) :
    Fin (inputCount + gateCount) :=
  Fin.castLE (Nat.le_add_right inputCount gateCount) input

theorem inputWire_eq_castAdd {inputCount gateCount : Nat}
    (input : Fin inputCount) :
    inputWire (gateCount := gateCount) input = Fin.castAdd gateCount input :=
  rfl

/-- Evaluate every wire, including the complete sequential gate trace. -/
def trace {inputCount : Nat} : {gateCount : Nat} →
    Circuit inputCount gateCount → (Fin inputCount → Bool) →
      Fin (inputCount + gateCount) → Bool
  | 0, .nil, input => input
  | _ + 1, .snoc circuit left right, input =>
      Fin.lastCases
        (!(trace circuit input left && trace circuit input right))
        (trace circuit input)

/-- Evaluate a designated output wire of the circuit. -/
def eval {inputCount gateCount : Nat} (circuit : Circuit inputCount gateCount)
    (output : Fin (inputCount + gateCount)) (input : Fin inputCount → Bool) : Bool :=
  trace circuit input output

@[simp] theorem eval_eq_trace {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (output : Fin (inputCount + gateCount))
    (input : Fin inputCount → Bool) :
    eval circuit output input = trace circuit input output := rfl

@[simp] theorem trace_nil {inputCount : Nat} (input : Fin inputCount → Bool) :
    trace (.nil : Circuit inputCount 0) input = input := rfl

@[simp] theorem trace_snoc_castSucc {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (left right wire : Fin (inputCount + gateCount))
    (input : Fin inputCount → Bool) :
    trace (.snoc circuit left right) input wire.castSucc = trace circuit input wire := by
  simp [trace]

@[simp] theorem trace_snoc_last {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (left right : Fin (inputCount + gateCount))
    (input : Fin inputCount → Bool) :
    trace (.snoc circuit left right) input (Fin.last (inputCount + gateCount)) =
      !(trace circuit input left && trace circuit input right) := by
  simp [trace]

@[simp] theorem inputWire_succ {inputCount gateCount : Nat} (input : Fin inputCount) :
    inputWire (gateCount := gateCount + 1) input =
      (inputWire (gateCount := gateCount) input).castSucc := by
  rfl

@[simp] theorem trace_inputWire {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (input : Fin inputCount → Bool)
    (index : Fin inputCount) :
    trace circuit input (inputWire (gateCount := gateCount) index) = input index := by
  induction circuit with
  | nil => rfl
  | snoc circuit left right ih =>
      simpa using ih

/-- Map a NAND constraint along a function on wire names. -/
def mapConstraint {Var Var' : Type} (mapWire : Var → Var')
    (constraint : NANDConstraint Var) : NANDConstraint Var' where
  input₁ := mapWire constraint.input₁
  input₂ := mapWire constraint.input₂
  output := mapWire constraint.output

@[simp] theorem mapConstraint_isSatisfied_iff {Var Var' : Type}
    (mapWire : Var → Var') (constraint : NANDConstraint Var)
    (assignment : Var' → Bool) :
    (mapConstraint mapWire constraint).IsSatisfied assignment ↔
      constraint.IsSatisfied (assignment ∘ mapWire) := by
  rfl

/-- The constraint for the final gate in a `snoc` circuit. -/
def lastConstraint {inputCount gateCount : Nat}
    (left right : Fin (inputCount + gateCount)) :
    NANDConstraint (Fin (inputCount + (gateCount + 1))) where
  input₁ := left.castSucc
  input₂ := right.castSucc
  output := Fin.last (inputCount + gateCount)

/-- Compile every sequential NAND gate into a quadratic NAND constraint. -/
def constraints {inputCount : Nat} : {gateCount : Nat} →
    Circuit inputCount gateCount →
      List (NANDConstraint (Fin (inputCount + gateCount)))
  | 0, .nil => []
  | _ + 1, .snoc circuit left right =>
      (constraints circuit).map (mapConstraint Fin.castSucc) ++ [lastConstraint left right]

@[simp] theorem constraints_nil {inputCount : Nat} :
    constraints (.nil : Circuit inputCount 0) = [] := rfl

@[simp] theorem constraints_snoc {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (left right : Fin (inputCount + gateCount)) :
    constraints (.snoc circuit left right) =
      (constraints circuit).map (mapConstraint Fin.castSucc) ++ [lastConstraint left right] := rfl

/-- Compilation produces exactly one quadratic constraint per NAND gate. -/
theorem constraints_length {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) :
    (constraints circuit).length = gateCount := by
  induction circuit with
  | nil => rfl
  | snoc circuit left right ih =>
      simp [ih]

/-- Restrict a total wire assignment to all wires preceding the final gate. -/
def dropLast {wireCount : Nat} (assignment : Fin (wireCount + 1) → Bool) :
    Fin wireCount → Bool :=
  fun wire => assignment wire.castSucc

@[simp] theorem dropLast_trace_snoc {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (left right : Fin (inputCount + gateCount))
    (input : Fin inputCount → Bool) :
    dropLast (wireCount := inputCount + gateCount)
        (trace (inputCount := inputCount) (gateCount := gateCount + 1)
          (.snoc circuit left right) input) =
      trace (inputCount := inputCount) (gateCount := gateCount) circuit input := by
  funext wire
  simp [dropLast]

/-- Mapping all wire names commutes with satisfaction after restricting an assignment. -/
theorem satisfies_mapConstraint_iff {Var Var' : Type} (mapWire : Var → Var')
    (source : List (NANDConstraint Var)) (assignment : Var' → Bool) :
    SatisfiesNANDConstraints (source.map (mapConstraint mapWire)) assignment ↔
      SatisfiesNANDConstraints source (assignment ∘ mapWire) := by
  constructor
  · intro hSatisfies constraint hMember
    apply (mapConstraint_isSatisfied_iff mapWire constraint assignment).mp
    exact hSatisfies _ (List.mem_map_of_mem (f := mapConstraint mapWire) hMember)
  · intro hSatisfies mappedConstraint hMember
    rcases List.mem_map.mp hMember with ⟨constraint, hConstraint, rfl⟩
    apply (mapConstraint_isSatisfied_iff mapWire constraint assignment).mpr
    exact hSatisfies constraint hConstraint

/-- Appending one constraint conjoins its satisfaction condition. -/
theorem satisfies_append_singleton_iff {Var : Type}
    (source : List (NANDConstraint Var)) (last : NANDConstraint Var)
    (assignment : Var → Bool) :
    SatisfiesNANDConstraints (source ++ [last]) assignment ↔
      SatisfiesNANDConstraints source assignment ∧ last.IsSatisfied assignment := by
  constructor
  · intro hSatisfies
    constructor
    · intro constraint hMember
      exact hSatisfies constraint (List.mem_append_left [last] hMember)
    · exact hSatisfies last (by simp)
  · rintro ⟨hSource, hLast⟩ constraint hMember
    rw [List.mem_append] at hMember
    rcases hMember with hMember | hMember
    · exact hSource constraint hMember
    · have hEquality : constraint = last := by simpa using hMember
      subst constraint
      exact hLast

@[simp] theorem satisfies_constraints_snoc_iff {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (left right : Fin (inputCount + gateCount))
    (assignment : Fin (inputCount + (gateCount + 1)) → Bool) :
    SatisfiesNANDConstraints (constraints (.snoc circuit left right)) assignment ↔
      SatisfiesNANDConstraints (constraints circuit) (dropLast assignment) ∧
        assignment (Fin.last (inputCount + gateCount)) =
          !(assignment left.castSucc && assignment right.castSucc) := by
  rw [constraints_snoc, satisfies_append_singleton_iff, satisfies_mapConstraint_iff]
  rfl

/-- The computed trace satisfies every compiled NAND constraint. -/
theorem trace_satisfies_constraints {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (input : Fin inputCount → Bool) :
    SatisfiesNANDConstraints (constraints circuit) (trace circuit input) := by
  induction circuit with
  | nil => simp [SatisfiesNANDConstraints]
  | snoc circuit left right ih =>
      rw [satisfies_constraints_snoc_iff]
      constructor
      · simpa only [dropLast_trace_snoc] using ih
      · simp

/-- A total assignment agrees with a chosen assignment on the circuit inputs. -/
def AgreesOnInputs {inputCount gateCount : Nat}
    (assignment : Fin (inputCount + gateCount) → Bool)
    (input : Fin inputCount → Bool) : Prop :=
  ∀ index, assignment (inputWire (gateCount := gateCount) index) = input index

/-- Restrict a total wire assignment to its input wires. -/
def inputRestriction {inputCount gateCount : Nat}
    (assignment : Fin (inputCount + gateCount) → Bool) : Fin inputCount → Bool :=
  fun index => assignment (inputWire (gateCount := gateCount) index)

@[simp] theorem agreesOnInputs_inputRestriction {inputCount gateCount : Nat}
    (assignment : Fin (inputCount + gateCount) → Bool) :
    AgreesOnInputs assignment (inputRestriction assignment) := by
  intro index
  rfl

/-- A satisfying wire assignment extending fixed inputs is the computed trace. -/
theorem eq_trace_of_satisfies_of_agrees {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (input : Fin inputCount → Bool)
    (assignment : Fin (inputCount + gateCount) → Bool)
    (hSatisfies : SatisfiesNANDConstraints (constraints circuit) assignment)
    (hInputs : AgreesOnInputs assignment input) :
    assignment = trace circuit input := by
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
      have hPreviousTrace : dropLast assignment = trace circuit input :=
        ih (dropLast assignment) hPrevious hPreviousInputs
      funext wire
      refine Fin.lastCases ?_ (fun previousWire => ?_) wire
      · calc
          assignment (Fin.last (inputCount + gateCount)) =
              !(assignment left.castSucc && assignment right.castSucc) := hLast
          _ = !(trace circuit input left && trace circuit input right) := by
              rw [← hPreviousTrace]
              rfl
          _ = trace (.snoc circuit left right) input
              (Fin.last (inputCount + gateCount)) := by
              rw [trace_snoc_last]
      · simpa [dropLast] using congrFun hPreviousTrace previousWire

/-- Every satisfying assignment is the unique trace over its own input restriction. -/
theorem eq_trace_inputRestriction_of_satisfies {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount)
    (assignment : Fin (inputCount + gateCount) → Bool)
    (hSatisfies : SatisfiesNANDConstraints (constraints circuit) assignment) :
    assignment = trace circuit (inputRestriction assignment) :=
  eq_trace_of_satisfies_of_agrees circuit (inputRestriction assignment) assignment
    hSatisfies (agreesOnInputs_inputRestriction assignment)

/-- Satisfying assignments extending fixed inputs are exactly the computed trace. -/
theorem satisfies_and_agrees_iff_eq_trace {inputCount gateCount : Nat}
    (circuit : Circuit inputCount gateCount) (input : Fin inputCount → Bool)
    (assignment : Fin (inputCount + gateCount) → Bool) :
    SatisfiesNANDConstraints (constraints circuit) assignment ∧
        AgreesOnInputs assignment input ↔
      assignment = trace circuit input := by
  constructor
  · rintro ⟨hSatisfies, hInputs⟩
    exact eq_trace_of_satisfies_of_agrees circuit input assignment hSatisfies hInputs
  · intro hAssignment
    subst assignment
    exact ⟨trace_satisfies_constraints circuit input, fun index => trace_inputWire circuit input index⟩

end Circuit
end NANDCircuit
end KLocality
