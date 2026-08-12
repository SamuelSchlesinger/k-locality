import KLocality.QuadraticNAND

namespace KLocality

/-!
# Tactics for finite Boolean locality proofs

The paper repeatedly uses three small proof moves: expand a syntactic
pseudo-Boolean polynomial, exhaust a handful of Boolean inputs, and discharge
the scope-cardinality side condition of a local energy.  This module packages
those moves without adding any trusted code: each tactic only assembles kernel
checked simplification, arithmetic, and existing locality lemmas.
-/

namespace Tactic

open Lean Parser.Tactic Elab.Tactic

/-- Normalize a syntactic quadratic pseudo-Boolean expression.

Extra definitions can be supplied as simp arguments, for example
`kpoly_norm [myPenalty]`. -/
syntax (name := kpolyNorm) "kpoly_norm" (simpArgs)? : tactic

macro_rules
  | `(tactic| kpoly_norm) =>
      `(tactic| (simp_all <;> norm_num <;> ring_nf))
  | `(tactic| kpoly_norm [$simpArgs,*]) =>
      `(tactic|
        (simp only [$simpArgs,*] at * <;>
          simp_all <;>
          norm_num <;> ring_nf))

/-- Exhaust the named Boolean variables and normalize each truth-table row.

This is deliberately explicit about the variables being split: it never
silently enumerates an assignment space whose size may be exponential.
Use `kpoly_norm [definitions]` first when the goal contains a project-specific
wrapper around the polynomial expression. -/
syntax (name := kboolCases) "kbool_cases" (ppSpace colGt ident)* : tactic

macro_rules
  | `(tactic| kbool_cases) => `(tactic| kpoly_norm)
  | `(tactic| kbool_cases $x:ident $xs:ident*) =>
      `(tactic| cases $x:ident <;> kbool_cases $xs*)

/- Existing locality constructors exposed to the focused `aesop` search used
by `klocality`. -/
attribute [aesop safe apply]
  KLocality.QuadraticNAND.QuadraticPolynomial.toLocalEnergy_respects_two
  KLocality.localEnergyConstraints_respectK
  KLocality.marginalConstraintsRespectK_mono

/-- Discharge standard scope bounds using the registered locality constructors,
small concrete scope expressions, and natural-number arithmetic.  Callers may
provide extra simp lemmas as in `klocality [myTerms]`. -/
syntax (name := kLocality) "klocality" (simpArgs)? : tactic

macro_rules
  | `(tactic| klocality) =>
      `(tactic| (aesop <;> omega))
  | `(tactic| klocality [$simpArgs,*]) =>
      `(tactic|
        (simp only [$simpArgs,*] at * <;> aesop <;> omega))

end Tactic

open Tactic
open QuadraticNAND

section Examples

example (a b c : Bool) : 0 ≤ phiNAND a b c := by
  simp [phiNAND]
  kbool_cases a b c

example {Var : Type*} [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var) :
    LocalEnergyTermsRespectK 2 polynomial.toLocalEnergy := by
  klocality

end Examples

end KLocality
