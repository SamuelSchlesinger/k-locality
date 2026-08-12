import KLocality.MaxSupport
import KLocality.UniversalExistence

namespace KLocality

open scoped BigOperators

universe u

/-!
# Canonical pseudo-Boolean feature polynomials

An order-`k` feature polynomial is represented by one real coefficient for
each Boolean monomial of degree at most `k`.  This is the native language of
the paper's exposing energies and Gibbs log-densities.
-/

/-- Coefficients of a multilinear Boolean polynomial of degree at most `k`. -/
abbrev FeaturePolynomial
    (Var : Type u) [DecidableEq Var] (k : Nat) :=
  FeatureScope Var k → ℝ

namespace FeaturePolynomial

/-- The linear functional taking a real weight table to one monomial moment. -/
noncomputable def momentFunctional
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (scope : FeatureScope Var k) :
    (Assignment Var → ℝ) →ₗ[ℝ] ℝ where
  toFun weights := ∑ x, weights x * monomialValue scope.1 x
  map_add' left right := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar weights := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- The linear moment map collecting every feature of order at most `k`. -/
noncomputable def momentMap
    {Var : Type u} [Fintype Var] [DecidableEq Var] (k : Nat) :
    (Assignment Var → ℝ) →ₗ[ℝ] (FeatureScope Var k → ℝ) :=
  LinearMap.pi momentFunctional

@[simp]
theorem momentMap_apply
    {Var : Type u} [Fintype Var] [DecidableEq Var] (k : Nat)
    (weights : Assignment Var → ℝ) (scope : FeatureScope Var k) :
    momentMap k weights scope =
      ∑ x, weights x * monomialValue scope.1 x :=
  rfl

@[simp]
theorem momentFunctional_single
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (scope : FeatureScope Var k) (x : Assignment Var) :
    momentFunctional scope (Pi.single x 1) = monomialValue scope.1 x := by
  classical
  simp [momentFunctional, Pi.single_apply]

/-- Real point-mass table underlying a PMF. -/
noncomputable def realWeights
    {Var : Type u} (p : Distribution (Assignment Var)) :
    Assignment Var → ℝ :=
  fun x => (p x).toReal

theorem momentMap_realWeights
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) (scope : FeatureScope Var k) :
    momentMap k (realWeights p) scope = monomialMoment p scope.1 := by
  rw [momentMap_apply, monomialMoment_eq_expectation]
  rfl

theorem sameFeatureMomentsUpTo_iff_momentMap_realWeights_eq
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p q : Distribution (Assignment Var)) :
    SameFeatureMomentsUpTo k p q ↔
      momentMap k (realWeights q) = momentMap k (realWeights p) := by
  constructor
  · intro h
    funext scope
    rw [momentMap_realWeights, momentMap_realWeights]
    exact h scope.1 scope.2
  · intro h scope hScope
    let indexedScope : FeatureScope Var k := ⟨scope, hScope⟩
    calc
      monomialMoment q scope = momentMap k (realWeights q) indexedScope := by
        symm
        exact momentMap_realWeights k q indexedScope
      _ = momentMap k (realWeights p) indexedScope := congrFun h indexedScope
      _ = monomialMoment p scope := momentMap_realWeights k p indexedScope

/-- Evaluate a canonical feature polynomial on a Boolean assignment. -/
noncomputable def eval
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) (x : Assignment Var) : ℝ :=
  ∑ scope : FeatureScope Var k,
    polynomial scope * monomialValue scope.1 x

/-- Expected value of a feature polynomial is the dot product of its
coefficients with the corresponding monomial moments. -/
theorem expectation_eval
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k)
    (p : Distribution (Assignment Var)) :
    pmfExpectation p (eval polynomial) =
      ∑ scope : FeatureScope Var k,
        polynomial scope * monomialMoment p scope.1 := by
  classical
  unfold pmfExpectation eval
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro scope _
  calc
    ∑ x, (p x).toReal *
        (polynomial scope * monomialValue scope.1 x) =
        ∑ x, polynomial scope *
          ((p x).toReal * monomialValue scope.1 x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = polynomial scope *
        ∑ x, (p x).toReal * monomialValue scope.1 x := by
          rw [Finset.mul_sum]
    _ = polynomial scope * monomialMoment p scope.1 := by
          rw [monomialMoment_eq_expectation]
          rfl

theorem expectation_eval_eq_of_sameFeatureMoments
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k)
    {p q : Distribution (Assignment Var)}
    (hMoments : SameFeatureMomentsUpTo k p q) :
    pmfExpectation q (eval polynomial) =
      pmfExpectation p (eval polynomial) := by
  rw [expectation_eval, expectation_eval]
  apply Finset.sum_congr rfl
  intro scope _
  rw [hMoments scope.1 scope.2]

/-- Convert one canonical feature monomial into a scoped local-energy term. -/
noncomputable def monomialTerm
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) (scope : FeatureScope Var k) :
    LocalEnergyTerm Var where
  scope := scope.1
  value := fun assignment =>
    polynomial scope * monomialValue (Finset.univ : Finset scope.1) assignment

/-- Convert a feature polynomial into its finite list of scoped monomial
terms. -/
noncomputable def toLocalEnergy
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) : List (LocalEnergyTerm Var) :=
  (Finset.univ : Finset (FeatureScope Var k)).toList.map
    (monomialTerm polynomial)

theorem toLocalEnergy_respectsK
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) :
    LocalEnergyTermsRespectK k polynomial.toLocalEnergy := by
  classical
  intro term hTerm
  rcases List.mem_map.mp hTerm with ⟨scope, _hScope, rfl⟩
  exact scope.2

@[simp]
theorem monomialTerm_eval
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) (scope : FeatureScope Var k)
    (x : Assignment Var) :
    (monomialTerm polynomial scope).eval x =
      polynomial scope * monomialValue scope.1 x := by
  classical
  simp only [monomialTerm, LocalEnergyTerm.eval]
  rw [monomialValue_restrict, liftSubscope_univ]

theorem localEnergyEval_toLocalEnergy
    {Var : Type u} [Fintype Var] [DecidableEq Var] {k : Nat}
    (polynomial : FeaturePolynomial Var k) (x : Assignment Var) :
    localEnergyEval polynomial.toLocalEnergy x = polynomial.eval x := by
  classical
  simp [toLocalEnergy, localEnergyEval, eval]

/-- The constant feature, present at every order. -/
def emptyScope
    (Var : Type u) [DecidableEq Var] (k : Nat) : FeatureScope Var k :=
  ⟨∅, by simp⟩

@[simp]
theorem monomialValue_empty
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (x : Assignment Var) :
    monomialValue (∅ : Finset Var) x = 1 := by
  simp [monomialValue]

end FeaturePolynomial

/-- A support is facial for the order-`k` marginal polytope when it is the
zero set of a nonnegative order-`k` feature polynomial.  For a finite
polytope this is equivalent to being the inverse image of an exposed face. -/
def IsFacialSupport
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (target : Set (Assignment Var)) : Prop :=
  ∃ energy : FeaturePolynomial Var k,
    (∀ x, 0 ≤ energy.eval x) ∧
      ∀ x, energy.eval x = 0 ↔ x ∈ target

/-- The logarithm of `p` is an order-`k` feature polynomial on its positive
support.  The constant feature absorbs the log-partition function. -/
def IsFeatureGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) : Prop :=
  ∃ theta : FeaturePolynomial Var k,
    ∀ x ∈ p.support, Real.log (p x).toReal = theta.eval x

/-- Certificate form of the paper's face--Gibbs condition. -/
def IsFaceGibbs
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) : Prop :=
  IsFacialSupport k p.support ∧ IsFeatureGibbs k p

end KLocality
