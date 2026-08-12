import KLocality.FeatureEmbedding
import KLocality.QuadraticNAND

namespace KLocality
namespace QuadraticNAND

universe u

/-!
# Quadratic NAND polynomials as canonical feature polynomials

`QuadraticNAND` deliberately represents quadratic pseudo-Boolean
polynomials syntactically, while the face--Gibbs theory uses the canonical
monomial basis.  This file gives the exact bridge between those two
representations.
-/

namespace QuadraticTerm

/-- The integer coefficient carried by a syntactic quadratic term. -/
def coefficient {Var : Type u} : QuadraticTerm Var -> ℤ
  | .constant value => value
  | .linear value _ => value
  | .pair value _ _ => value

/-- The variables of a quadratic term, bundled with the degree-two bound. -/
def featureScope {Var : Type u} [DecidableEq Var]
    (term : QuadraticTerm Var) : FeatureScope Var 2 :=
  ⟨term.scope, term.scope_card_le_two⟩

/-- A syntactic quadratic term in the canonical Boolean monomial basis. -/
noncomputable def toFeaturePolynomial
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (term : QuadraticTerm Var) : FeaturePolynomial Var 2 :=
  FeaturePolynomial.single term.featureScope term.coefficient

/-- Conversion to the canonical monomial basis preserves evaluation. -/
@[simp]
theorem eval_toFeaturePolynomial
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (term : QuadraticTerm Var) (assignment : Assignment Var) :
    term.toFeaturePolynomial.eval assignment = (term.eval assignment : ℝ) := by
  classical
  rw [toFeaturePolynomial, FeaturePolynomial.eval_single]
  cases term with
  | constant value =>
      simp [featureScope, scope, coefficient, monomialValue]
  | linear value coordinate =>
      cases hVariable : assignment coordinate <;>
        simp [featureScope, scope, coefficient, monomialValue, hVariable, bitInt]
  | pair value left right =>
      cases hLeft : assignment left <;> cases hRight : assignment right <;>
        simp [featureScope, scope, coefficient, monomialValue,
          Finset.insert_subset_iff, hLeft, hRight, bitInt]

end QuadraticTerm

namespace QuadraticPolynomial

/-- A syntactic quadratic polynomial in the canonical Boolean monomial
basis.  Repeated syntactic terms are accumulated by function addition. -/
noncomputable def toFeaturePolynomial
    {Var : Type u} [Fintype Var] [DecidableEq Var] :
    QuadraticPolynomial Var -> FeaturePolynomial Var 2
  | [] => 0
  | term :: polynomial =>
      term.toFeaturePolynomial + toFeaturePolynomial polynomial

/-- Conversion to the canonical monomial basis preserves evaluation. -/
@[simp]
theorem eval_toFeaturePolynomial
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (polynomial : QuadraticPolynomial Var) (assignment : Assignment Var) :
    polynomial.toFeaturePolynomial.eval assignment =
      (polynomial.eval assignment : ℝ) := by
  induction polynomial with
  | nil => simp [toFeaturePolynomial, FeaturePolynomial.eval]
  | cons term polynomial ih =>
      rw [toFeaturePolynomial, FeaturePolynomial.eval_add,
        QuadraticTerm.eval_toFeaturePolynomial, ih, eval_cons]
      norm_num

end QuadraticPolynomial

end QuadraticNAND
end KLocality
