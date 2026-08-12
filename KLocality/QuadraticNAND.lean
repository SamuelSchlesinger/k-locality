import KLocality.GroundState

namespace KLocality
namespace QuadraticNAND

universe u

/-!
# Quadratic NAND synthesis

This file isolates the truth-table kernel used by the quadratic NAND construction.
Quadraticity is enforced syntactically: a polynomial is a list of constants, linear
terms, and pairwise products.  In particular, there is no constructor for a monomial
of degree greater than two.
-/

/-- Embed a Boolean bit into the integers. -/
def bitInt (b : Bool) : ℤ :=
  if b then 1 else 0

@[simp] theorem bitInt_false : bitInt false = 0 := rfl

@[simp] theorem bitInt_true : bitInt true = 1 := rfl

/-- One term of a syntactically quadratic integer polynomial. -/
inductive QuadraticTerm (Var : Type u) where
  | constant (coefficient : ℤ)
  | linear (coefficient : ℤ) (var : Var)
  | pair (coefficient : ℤ) (left right : Var)

namespace QuadraticTerm

/-- Evaluate a quadratic term on a Boolean assignment. -/
def eval {Var : Type u} (assignment : Var → Bool) : QuadraticTerm Var → ℤ
  | .constant coefficient => coefficient
  | .linear coefficient var => coefficient * bitInt (assignment var)
  | .pair coefficient left right =>
      coefficient * bitInt (assignment left) * bitInt (assignment right)

@[simp] theorem eval_constant {Var : Type u} (assignment : Var → Bool) (coefficient : ℤ) :
    eval assignment (.constant coefficient) = coefficient := rfl

@[simp] theorem eval_linear {Var : Type u} (assignment : Var → Bool)
    (coefficient : ℤ) (var : Var) :
    eval assignment (.linear coefficient var) =
      coefficient * bitInt (assignment var) := rfl

@[simp] theorem eval_pair {Var : Type u} (assignment : Var → Bool)
    (coefficient : ℤ) (left right : Var) :
    eval assignment (.pair coefficient left right) =
      coefficient * bitInt (assignment left) * bitInt (assignment right) := rfl

/-- Rename the variables of one quadratic term. -/
def rename {Var Var' : Type*} (mapVar : Var → Var') :
    QuadraticTerm Var → QuadraticTerm Var'
  | .constant coefficient => .constant coefficient
  | .linear coefficient var => .linear coefficient (mapVar var)
  | .pair coefficient left right => .pair coefficient (mapVar left) (mapVar right)

@[simp]
theorem eval_rename {Var Var' : Type*} (mapVar : Var → Var')
    (assignment : Var' → Bool) (term : QuadraticTerm Var) :
    (term.rename mapVar).eval assignment = term.eval (assignment ∘ mapVar) := by
  cases term <;> rfl

/-- The variables on which a quadratic term depends. -/
def scope {Var : Type u} [DecidableEq Var] : QuadraticTerm Var → Finset Var
  | .constant _ => ∅
  | .linear _ var => {var}
  | .pair _ left right => {left, right}

/-- Regard a syntactic quadratic term as a real-valued scoped local energy term. -/
def toLocalEnergyTerm {Var : Type u} [DecidableEq Var]
    (term : QuadraticTerm Var) : LocalEnergyTerm Var :=
  match term with
  | .constant coefficient =>
      { scope := ∅
        value := fun _ => (coefficient : ℝ) }
  | .linear coefficient var =>
      { scope := {var}
        value := fun assignment =>
          (coefficient : ℝ) *
            (bitInt (assignment ⟨var, Finset.mem_singleton_self var⟩) : ℝ) }
  | .pair coefficient left right =>
      { scope := {left, right}
        value := fun assignment =>
          (coefficient : ℝ) *
              (bitInt (assignment ⟨left, Finset.mem_insert_self left {right}⟩) : ℝ) *
            (bitInt (assignment ⟨right,
              Finset.mem_insert_of_mem (Finset.mem_singleton_self right)⟩) : ℝ) }

@[simp]
theorem toLocalEnergyTerm_scope {Var : Type u} [DecidableEq Var]
    (term : QuadraticTerm Var) :
    term.toLocalEnergyTerm.scope = term.scope := by
  cases term <;> rfl

/-- Converting a quadratic term to a local term preserves its evaluation. -/
@[simp]
theorem eval_toLocalEnergyTerm {Var : Type u} [DecidableEq Var]
    (term : QuadraticTerm Var) (assignment : Var → Bool) :
    term.toLocalEnergyTerm.eval assignment = (term.eval assignment : ℝ) := by
  cases term with
  | constant coefficient => rfl
  | linear coefficient var =>
      simp [toLocalEnergyTerm, LocalEnergyTerm.eval, restrict, eval]
  | pair coefficient left right =>
      simp [toLocalEnergyTerm, LocalEnergyTerm.eval, restrict, eval]

/-- Every syntactic quadratic term uses at most two variables. -/
theorem scope_card_le_two {Var : Type u} [DecidableEq Var]
    (term : QuadraticTerm Var) :
    term.scope.card ≤ 2 := by
  cases term with
  | constant coefficient => simp [scope]
  | linear coefficient var => simp [scope]
  | pair coefficient left right =>
      simpa [scope] using Finset.card_insert_le left ({right} : Finset Var)

end QuadraticTerm

/-- A syntactically quadratic polynomial is a finite list of quadratic terms. -/
abbrev QuadraticPolynomial (Var : Type u) := List (QuadraticTerm Var)

namespace QuadraticPolynomial

/-- Evaluate a quadratic polynomial by summing its term evaluations. -/
def eval {Var : Type u} (assignment : Var → Bool) (polynomial : QuadraticPolynomial Var) : ℤ :=
  (polynomial.map (QuadraticTerm.eval assignment)).sum

@[simp] theorem eval_nil {Var : Type u} (assignment : Var → Bool) :
    eval assignment ([] : QuadraticPolynomial Var) = 0 := rfl

@[simp] theorem eval_cons {Var : Type u} (assignment : Var → Bool)
    (term : QuadraticTerm Var) (polynomial : QuadraticPolynomial Var) :
    eval assignment (term :: polynomial) =
      QuadraticTerm.eval assignment term + eval assignment polynomial := by
  simp [eval]

@[simp] theorem eval_append {Var : Type u} (assignment : Var → Bool)
    (left right : QuadraticPolynomial Var) :
    eval assignment (left ++ right) = eval assignment left + eval assignment right := by
  simp [eval]

/-- Evaluation commutes with assembling a polynomial by `List.flatMap`.
This is a useful normalization rule for families of local penalties. -/
@[simp]
theorem eval_flatMap {Var : Type u} {ι : Type*}
    (assignment : Var → Bool) (items : List ι)
    (penalty : ι → QuadraticPolynomial Var) :
    eval assignment (items.flatMap penalty) =
      (items.map fun item => eval assignment (penalty item)).sum := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp [ih]

/-- Rename every variable in a quadratic polynomial. -/
def renameVars {Var Var' : Type*} (mapVar : Var → Var')
    (polynomial : QuadraticPolynomial Var) : QuadraticPolynomial Var' :=
  polynomial.map (QuadraticTerm.rename mapVar)

@[simp]
theorem eval_renameVars {Var Var' : Type*} (mapVar : Var → Var')
    (assignment : Var' → Bool) (polynomial : QuadraticPolynomial Var) :
    (polynomial.renameVars mapVar).eval assignment =
      polynomial.eval (assignment ∘ mapVar) := by
  simp [renameVars, eval, List.map_map, Function.comp_def]

/-- Convert a quadratic polynomial into a sum of real-valued terms of scope at most two. -/
def toLocalEnergy {Var : Type u} [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var) : List (LocalEnergyTerm Var) :=
  polynomial.map QuadraticTerm.toLocalEnergyTerm

/-- Conversion to scoped local energy preserves polynomial evaluation. -/
theorem localEnergyEval_toLocalEnergy {Var : Type u} [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var) (assignment : Var → Bool) :
    localEnergyEval polynomial.toLocalEnergy assignment =
      (polynomial.eval assignment : ℝ) := by
  induction polynomial with
  | nil => simp [toLocalEnergy, localEnergyEval, eval]
  | cons term polynomial ih =>
      change term.toLocalEnergyTerm.eval assignment +
          localEnergyEval (toLocalEnergy polynomial) assignment =
        ((term.eval assignment + eval assignment polynomial : ℤ) : ℝ)
      rw [QuadraticTerm.eval_toLocalEnergyTerm, ih]
      norm_num

/-- The converted local energy has scope bound two. -/
theorem toLocalEnergy_respects_two {Var : Type u} [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var) :
    LocalEnergyTermsRespectK 2 polynomial.toLocalEnergy := by
  intro term hTerm
  rcases List.mem_map.mp hTerm with ⟨quadraticTerm, _hQuadraticTerm, rfl⟩
  simpa using quadraticTerm.scope_card_le_two

/-- The finite zero set of a quadratic polynomial. -/
noncomputable def groundStates {Var : Type u} [Fintype Var] [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var) : Finset (Var → Bool) := by
  classical
  exact Finset.univ.filter fun assignment => polynomial.eval assignment = 0

@[simp]
theorem mem_groundStates_iff {Var : Type u} [Fintype Var] [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var) (assignment : Var → Bool) :
    assignment ∈ polynomial.groundStates ↔ polynomial.eval assignment = 0 := by
  classical
  simp [groundStates]

/-- A nonnegative quadratic polynomial has a 2-local uniform ground-state law. -/
theorem uniformOn_groundStates_isTwoLocal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var)
    (hNonempty : polynomial.groundStates.Nonempty)
    (hNonneg : ∀ assignment, 0 ≤ polynomial.eval assignment) :
    IsKLocalMarginal 2 (uniformOn polynomial.groundStates hNonempty) := by
  apply uniformOn_isKLocalMarginal_of_localEnergy 2
      polynomial.groundStates hNonempty polynomial.toLocalEnergy
  · exact polynomial.toLocalEnergy_respects_two
  · intro assignment
    rw [polynomial.localEnergyEval_toLocalEnergy]
    exact_mod_cast hNonneg assignment
  · intro assignment
    rw [mem_groundStates_iff, polynomial.localEnergyEval_toLocalEnergy]
    norm_cast

end QuadraticPolynomial

/-- The quadratic NAND penalty
`3 - 2a - 2b - 3c + ab + 2ac + 2bc`. -/
def phiNAND (a b c : Bool) : ℤ :=
  3 - 2 * bitInt a - 2 * bitInt b - 3 * bitInt c
    + bitInt a * bitInt b
    + 2 * bitInt a * bitInt c
    + 2 * bitInt b * bitInt c

/-- The syntactically quadratic polynomial representing `phiNAND`. -/
def phiNANDPolynomial {Var : Type u} (a b c : Var) : QuadraticPolynomial Var :=
  [ .constant 3,
    .linear (-2) a,
    .linear (-2) b,
    .linear (-3) c,
    .pair 1 a b,
    .pair 2 a c,
    .pair 2 b c ]

@[simp] theorem eval_phiNANDPolynomial {Var : Type u} (assignment : Var → Bool)
    (a b c : Var) :
    QuadraticPolynomial.eval assignment (phiNANDPolynomial a b c) =
      phiNAND (assignment a) (assignment b) (assignment c) := by
  simp [phiNANDPolynomial, phiNAND, QuadraticPolynomial.eval]
  ring

/-- The NAND penalty is nonnegative on every Boolean input. -/
theorem phiNAND_nonneg (a b c : Bool) :
    0 ≤ phiNAND a b c := by
  cases a <;> cases b <;> cases c <;> norm_num [phiNAND, bitInt]

/-- The NAND penalty vanishes exactly on the graph of NAND. -/
theorem phiNAND_eq_zero_iff (a b c : Bool) :
    phiNAND a b c = 0 ↔ c = !(a && b) := by
  cases a <;> cases b <;> cases c <;> norm_num [phiNAND, bitInt]

/-- A single NAND constraint with two input wires and one output wire. -/
structure NANDConstraint (Var : Type u) where
  input₁ : Var
  input₂ : Var
  output : Var

namespace NANDConstraint

/-- A Boolean assignment satisfies a NAND constraint when its output is the NAND of its inputs. -/
def IsSatisfied {Var : Type u} (constraint : NANDConstraint Var)
    (assignment : Var → Bool) : Prop :=
  assignment constraint.output = !(assignment constraint.input₁ && assignment constraint.input₂)

/-- The quadratic polynomial attached to one NAND constraint. -/
def polynomial {Var : Type u} (constraint : NANDConstraint Var) : QuadraticPolynomial Var :=
  phiNANDPolynomial constraint.input₁ constraint.input₂ constraint.output

@[simp] theorem eval_polynomial {Var : Type u} (constraint : NANDConstraint Var)
    (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment constraint.polynomial =
      phiNAND (assignment constraint.input₁) (assignment constraint.input₂)
        (assignment constraint.output) := by
  simp [polynomial]

/-- Every single-constraint NAND polynomial evaluates nonnegatively. -/
theorem eval_polynomial_nonneg {Var : Type u} (constraint : NANDConstraint Var)
    (assignment : Var → Bool) :
    0 ≤ QuadraticPolynomial.eval assignment constraint.polynomial := by
  rw [eval_polynomial]
  exact phiNAND_nonneg _ _ _

/-- A single-constraint polynomial vanishes exactly when the constraint is satisfied. -/
theorem eval_polynomial_eq_zero_iff {Var : Type u} (constraint : NANDConstraint Var)
    (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment constraint.polynomial = 0 ↔
      constraint.IsSatisfied assignment := by
  rw [eval_polynomial, phiNAND_eq_zero_iff]
  rfl

end NANDConstraint

/-- Sum the quadratic penalties for a list of NAND constraints. -/
def nandHamiltonian {Var : Type u} : List (NANDConstraint Var) → QuadraticPolynomial Var
  | [] => []
  | constraint :: constraints => constraint.polynomial ++ nandHamiltonian constraints

/-- Every constraint in the list is satisfied by the assignment. -/
def SatisfiesNANDConstraints {Var : Type u} (constraints : List (NANDConstraint Var))
    (assignment : Var → Bool) : Prop :=
  ∀ constraint ∈ constraints, constraint.IsSatisfied assignment

@[simp] theorem satisfiesNANDConstraints_nil {Var : Type u} (assignment : Var → Bool) :
    SatisfiesNANDConstraints [] assignment := by
  simp [SatisfiesNANDConstraints]

@[simp] theorem satisfiesNANDConstraints_cons {Var : Type u}
    (constraint : NANDConstraint Var) (constraints : List (NANDConstraint Var))
    (assignment : Var → Bool) :
    SatisfiesNANDConstraints (constraint :: constraints) assignment ↔
      constraint.IsSatisfied assignment ∧ SatisfiesNANDConstraints constraints assignment := by
  simp [SatisfiesNANDConstraints]

@[simp] theorem eval_nandHamiltonian_nil {Var : Type u} (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment (nandHamiltonian ([] : List (NANDConstraint Var))) = 0 :=
  rfl

@[simp] theorem eval_nandHamiltonian_cons {Var : Type u}
    (constraint : NANDConstraint Var) (constraints : List (NANDConstraint Var))
    (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment (nandHamiltonian (constraint :: constraints)) =
      QuadraticPolynomial.eval assignment constraint.polynomial +
        QuadraticPolynomial.eval assignment (nandHamiltonian constraints) := by
  simp [nandHamiltonian]

/-- Evaluation of the Hamiltonian is the sum of the individual NAND penalties. -/
theorem eval_nandHamiltonian_eq_sum {Var : Type u}
    (constraints : List (NANDConstraint Var)) (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment (nandHamiltonian constraints) =
      (constraints.map fun constraint =>
        QuadraticPolynomial.eval assignment constraint.polynomial).sum := by
  induction constraints with
  | nil => simp
  | cons constraint constraints ih =>
      simp [ih]

/-- A sum of NAND penalties is nonnegative on every Boolean assignment. -/
theorem eval_nandHamiltonian_nonneg {Var : Type u}
    (constraints : List (NANDConstraint Var)) (assignment : Var → Bool) :
    0 ≤ QuadraticPolynomial.eval assignment (nandHamiltonian constraints) := by
  induction constraints with
  | nil => simp
  | cons constraint constraints ih =>
      rw [eval_nandHamiltonian_cons]
      exact add_nonneg (constraint.eval_polynomial_nonneg assignment) ih

/-- The summed Hamiltonian vanishes exactly when every NAND constraint is satisfied. -/
theorem eval_nandHamiltonian_eq_zero_iff {Var : Type u}
    (constraints : List (NANDConstraint Var)) (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment (nandHamiltonian constraints) = 0 ↔
      SatisfiesNANDConstraints constraints assignment := by
  induction constraints with
  | nil => simp
  | cons constraint constraints ih =>
      rw [eval_nandHamiltonian_cons]
      rw [add_eq_zero_iff_of_nonneg
        (constraint.eval_polynomial_nonneg assignment)
        (eval_nandHamiltonian_nonneg constraints assignment)]
      rw [constraint.eval_polynomial_eq_zero_iff, ih, satisfiesNANDConstraints_cons]

/-- The finite set of assignments satisfying every NAND constraint. -/
noncomputable def nandGroundStates {Var : Type u} [Fintype Var] [DecidableEq Var]
    (constraints : List (NANDConstraint Var)) : Finset (Var → Bool) := by
  classical
  exact Finset.univ.filter fun assignment =>
    SatisfiesNANDConstraints constraints assignment

theorem mem_nandGroundStates_iff {Var : Type u} [Fintype Var] [DecidableEq Var]
    (constraints : List (NANDConstraint Var)) (assignment : Var → Bool) :
    assignment ∈ nandGroundStates constraints ↔
      QuadraticPolynomial.eval assignment (nandHamiltonian constraints) = 0 := by
  classical
  simp only [nandGroundStates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (eval_nandHamiltonian_eq_zero_iff constraints assignment).symm

/-- The uniform law on any nonempty NAND ground space is a quadratic local model. -/
theorem uniformOn_nandGroundStates_isTwoLocal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (constraints : List (NANDConstraint Var))
    (hNonempty : (nandGroundStates constraints).Nonempty) :
    IsKLocalMarginal 2 (uniformOn (nandGroundStates constraints) hNonempty) := by
  let polynomial : QuadraticPolynomial Var := nandHamiltonian constraints
  let terms : List (LocalEnergyTerm Var) := polynomial.toLocalEnergy
  apply uniformOn_isKLocalMarginal_of_localEnergy 2
      (nandGroundStates constraints) hNonempty terms
  · exact QuadraticPolynomial.toLocalEnergy_respects_two polynomial
  · intro assignment
    rw [show localEnergyEval terms assignment =
        (QuadraticPolynomial.eval assignment polynomial : ℝ) by
      exact QuadraticPolynomial.localEnergyEval_toLocalEnergy polynomial assignment]
    exact_mod_cast eval_nandHamiltonian_nonneg constraints assignment
  · intro assignment
    rw [mem_nandGroundStates_iff]
    rw [show localEnergyEval terms assignment =
        (QuadraticPolynomial.eval assignment polynomial : ℝ) by
      exact QuadraticPolynomial.localEnergyEval_toLocalEnergy polynomial assignment]
    norm_cast

/-- Linear penalty `1 - x`, used to force a designated output wire to one. -/
def outputOnePenalty {Var : Type u} (output : Var) : QuadraticPolynomial Var :=
  [.constant 1, .linear (-1) output]

@[simp] theorem eval_outputOnePenalty {Var : Type u} (assignment : Var → Bool) (output : Var) :
    QuadraticPolynomial.eval assignment (outputOnePenalty output) =
      1 - bitInt (assignment output) := by
  simp [outputOnePenalty, QuadraticPolynomial.eval]
  ring

/-- The output-one penalty is nonnegative. -/
theorem eval_outputOnePenalty_nonneg {Var : Type u} (assignment : Var → Bool) (output : Var) :
    0 ≤ QuadraticPolynomial.eval assignment (outputOnePenalty output) := by
  rw [eval_outputOnePenalty]
  cases assignment output <;> norm_num

/-- The output-one penalty vanishes exactly when the designated output is true. -/
theorem eval_outputOnePenalty_eq_zero_iff {Var : Type u}
    (assignment : Var → Bool) (output : Var) :
    QuadraticPolynomial.eval assignment (outputOnePenalty output) = 0 ↔
      assignment output = true := by
  rw [eval_outputOnePenalty]
  cases assignment output <;> norm_num

/-- NAND-constraint Hamiltonian with a linear penalty forcing the designated output to one. -/
def nandRecognizerHamiltonian {Var : Type u}
    (constraints : List (NANDConstraint Var)) (output : Var) : QuadraticPolynomial Var :=
  nandHamiltonian constraints ++ outputOnePenalty output

@[simp]
theorem eval_nandRecognizerHamiltonian {Var : Type u}
    (constraints : List (NANDConstraint Var)) (output : Var) (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment (nandRecognizerHamiltonian constraints output) =
      QuadraticPolynomial.eval assignment (nandHamiltonian constraints) +
        QuadraticPolynomial.eval assignment (outputOnePenalty output) := by
  simp [nandRecognizerHamiltonian]

/-- The recognizer Hamiltonian is nonnegative. -/
theorem eval_nandRecognizerHamiltonian_nonneg {Var : Type u}
    (constraints : List (NANDConstraint Var)) (output : Var) (assignment : Var → Bool) :
    0 ≤ QuadraticPolynomial.eval assignment
      (nandRecognizerHamiltonian constraints output) := by
  rw [eval_nandRecognizerHamiltonian]
  exact add_nonneg (eval_nandHamiltonian_nonneg constraints assignment)
    (eval_outputOnePenalty_nonneg assignment output)

/-- The recognizer Hamiltonian vanishes exactly on satisfying assignments with output one. -/
theorem eval_nandRecognizerHamiltonian_eq_zero_iff {Var : Type u}
    (constraints : List (NANDConstraint Var)) (output : Var) (assignment : Var → Bool) :
    QuadraticPolynomial.eval assignment (nandRecognizerHamiltonian constraints output) = 0 ↔
      SatisfiesNANDConstraints constraints assignment ∧ assignment output = true := by
  rw [eval_nandRecognizerHamiltonian]
  rw [add_eq_zero_iff_of_nonneg
    (eval_nandHamiltonian_nonneg constraints assignment)
    (eval_outputOnePenalty_nonneg assignment output)]
  rw [eval_nandHamiltonian_eq_zero_iff, eval_outputOnePenalty_eq_zero_iff]

/-- The finite set of accepting assignments for a NAND constraint system. -/
def nandAcceptingGroundStates {Var : Type u} [Fintype Var] [DecidableEq Var]
    (constraints : List (NANDConstraint Var)) (output : Var) : Finset (Var → Bool) :=
  Finset.univ.filter fun assignment =>
    QuadraticPolynomial.eval assignment (nandRecognizerHamiltonian constraints output) = 0

@[simp]
theorem mem_nandAcceptingGroundStates_iff {Var : Type u} [Fintype Var] [DecidableEq Var]
    (constraints : List (NANDConstraint Var)) (output : Var) (assignment : Var → Bool) :
    assignment ∈ nandAcceptingGroundStates constraints output ↔
      QuadraticPolynomial.eval assignment (nandRecognizerHamiltonian constraints output) = 0 := by
  simp [nandAcceptingGroundStates]

/-- Membership in the accepting ground space has the direct constraint semantics. -/
theorem mem_nandAcceptingGroundStates_iff_satisfies
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (constraints : List (NANDConstraint Var)) (output : Var) (assignment : Var → Bool) :
    assignment ∈ nandAcceptingGroundStates constraints output ↔
      SatisfiesNANDConstraints constraints assignment ∧ assignment output = true := by
  rw [mem_nandAcceptingGroundStates_iff,
    eval_nandRecognizerHamiltonian_eq_zero_iff]

/-- The uniform law on a nonempty accepting NAND ground space is a quadratic local model. -/
theorem uniformOn_nandAcceptingGroundStates_isTwoLocal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (constraints : List (NANDConstraint Var)) (output : Var)
    (hNonempty : (nandAcceptingGroundStates constraints output).Nonempty) :
    IsKLocalMarginal 2
      (uniformOn (nandAcceptingGroundStates constraints output) hNonempty) := by
  let polynomial : QuadraticPolynomial Var :=
    nandRecognizerHamiltonian constraints output
  let terms : List (LocalEnergyTerm Var) := polynomial.toLocalEnergy
  apply uniformOn_isKLocalMarginal_of_localEnergy 2
      (nandAcceptingGroundStates constraints output) hNonempty terms
  · exact QuadraticPolynomial.toLocalEnergy_respects_two polynomial
  · intro assignment
    rw [show localEnergyEval terms assignment =
        (QuadraticPolynomial.eval assignment polynomial : ℝ) by
      exact QuadraticPolynomial.localEnergyEval_toLocalEnergy polynomial assignment]
    exact_mod_cast eval_nandRecognizerHamiltonian_nonneg constraints output assignment
  · intro assignment
    rw [mem_nandAcceptingGroundStates_iff]
    rw [show localEnergyEval terms assignment =
        (QuadraticPolynomial.eval assignment polynomial : ℝ) by
      exact QuadraticPolynomial.localEnergyEval_toLocalEnergy polynomial assignment]
    norm_cast

/-- Quadratic penalty `x + y - 2xy`, used to force two wires to be equal. -/
def equalityPenalty {Var : Type u} (left right : Var) : QuadraticPolynomial Var :=
  [.linear 1 left, .linear 1 right, .pair (-2) left right]

@[simp] theorem eval_equalityPenalty {Var : Type u} (assignment : Var → Bool)
    (left right : Var) :
    QuadraticPolynomial.eval assignment (equalityPenalty left right) =
      bitInt (assignment left) + bitInt (assignment right)
        - 2 * bitInt (assignment left) * bitInt (assignment right) := by
  simp [equalityPenalty, QuadraticPolynomial.eval]
  ring

/-- The equality penalty is nonnegative. -/
theorem eval_equalityPenalty_nonneg {Var : Type u} (assignment : Var → Bool)
    (left right : Var) :
    0 ≤ QuadraticPolynomial.eval assignment (equalityPenalty left right) := by
  rw [eval_equalityPenalty]
  generalize assignment left = a
  generalize assignment right = b
  cases a <;> cases b <;> norm_num

/-- The equality penalty vanishes exactly when the two designated bits agree. -/
theorem eval_equalityPenalty_eq_zero_iff {Var : Type u} (assignment : Var → Bool)
    (left right : Var) :
    QuadraticPolynomial.eval assignment (equalityPenalty left right) = 0 ↔
      assignment left = assignment right := by
  rw [eval_equalityPenalty]
  generalize hleft : assignment left = a
  generalize hright : assignment right = b
  cases a <;> cases b <;> norm_num

end QuadraticNAND
end KLocality
