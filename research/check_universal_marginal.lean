import KLocality
import Lean.Util.CollectAxioms

/-! Reproducible trust audit and executable identity checks for the two general theorems.

Run with `lake env lean -DwarningAsError=true research/check_universal_marginal.lean`.
The finite executions below test the implementation; the uniform correctness theorem,
which is audited separately, does not depend on those executions.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name := #[
    ``KLocality.localizationComplexity_le_min_supportCard_balancedLiftBound,
    ``KLocality.localizationComplexity_isBigO_exp,
    ``KLocality.MarginalVariety.projectiveVariety_eq_zariskiClosure,
    ``KLocality.MarginalVariety.projectiveParameterImage_eq_unscaled,
    ``KLocality.MarginalVariety.projectiveDistribution_mem_of_localizationComplexity_le,
    ``KLocality.MarginalVariety.localizationComplexity_gt_of_homogeneous_polynomial,
    ``KLocality.MarginalVariety.projectiveDimension_le,
    ``KLocality.MarginalVariety.exists_homogeneous_integer_certificate,
    ``KLocality.MarginalVariety.ideal_eq_elimination,
    ``KLocality.MarginalVariety.ideal_finitely_generated,
    ``KLocality.MarginalVariety.checkIdentity_iff_elimination,
    ``KLocality.RationalPolynomialExpression.value_surjective]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
  logInfo m!"Axiom audit passed for {declarations.size} declarations."

namespace KLocality

private def cell (a b : Bool) : BitVec 2 := ![a, b]

private def determinant : RationalPolynomialExpression (BitVec 2) :=
  .add (.mul (.atom (cell false false)) (.atom (cell true true)))
    (.mul (.constant (-1)) (.mul (.atom (cell false true)) (.atom (cell true false))))

private def normalization : RationalPolynomialExpression (BitVec 1) :=
  .add (.add (.atom (fun _ => false)) (.atom (fun _ => true))) (.constant (-1))

private def fourCells (a b c d : BitVec 3) : RationalPolynomialExpression (BitVec 3) :=
  .mul (.mul (.atom a) (.atom b)) (.mul (.atom c) (.atom d))

private def cubicOddsRatio : RationalPolynomialExpression (BitVec 3) :=
  .add (fourCells ![false, false, false] ![false, true, true]
    ![true, false, true] ![true, true, false])
    (.mul (.constant (-1)) (fourCells ![false, false, true] ![false, true, false]
      ![true, false, false] ![true, true, true]))

#eval show IO Unit from do
  let cases : List (String × Bool × Bool) := [
    ("independence determinant, unary, no hidden bit",
      MarginalVariety.checkIdentity (H := Fin 0) 1 determinant, true),
    ("independence determinant, unary, one hidden bit",
      MarginalVariety.checkIdentity (H := Fin 1) 1 determinant, true),
    ("independence determinant, quadratic, no hidden bit",
      MarginalVariety.checkIdentity (H := Fin 0) 2 determinant, false),
    ("independence determinant, quadratic, one hidden bit",
      MarginalVariety.checkIdentity (H := Fin 1) 2 determinant, false),
    ("nonzero constant, empty visible and hidden types",
      MarginalVariety.checkIdentity (V := Fin 0) (H := Fin 0) 2 (.constant 1), false),
    ("normalization is not an equation of the affine cone",
      MarginalVariety.checkIdentity (H := Fin 0) 2 normalization, false),
    ("cubic odds ratio, quadratic, no hidden bit",
      MarginalVariety.checkIdentity (H := Fin 0) 2 cubicOddsRatio, true),
    ("cubic odds ratio, quadratic, one hidden bit",
      MarginalVariety.checkIdentity (H := Fin 1) 2 cubicOddsRatio, false)]
  for (label, actual, expected) in cases do
    unless actual == expected do
      throw (IO.userError s!"Identity check failed: {label}")
  IO.println s!"Executable identity checks passed: {cases.length}."

end KLocality
