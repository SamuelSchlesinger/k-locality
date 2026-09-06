import KLocality.MarginalVarietyElimination
import Mathlib.Algebra.BigOperators.Ring.Multiset

namespace KLocality

open scoped BigOperators
open MvPolynomial

/-- Finite arithmetic syntax for a rational polynomial. -/
inductive RationalPolynomialExpression (A : Type)
  | constant : ℚ → RationalPolynomialExpression A
  | atom : A → RationalPolynomialExpression A
  | add : RationalPolynomialExpression A → RationalPolynomialExpression A → RationalPolynomialExpression A
  | mul : RationalPolynomialExpression A → RationalPolynomialExpression A → RationalPolynomialExpression A

namespace RationalPolynomialExpression

noncomputable def value {A : Type} : RationalPolynomialExpression A → MvPolynomial A ℚ
  | constant c => C c
  | atom a => X a
  | add f g => value f + value g
  | mul f g => value f * value g

theorem value_surjective {A : Type} : Function.Surjective (@value A) := by
  intro f
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨constant c, rfl⟩
  | add f g hf hg =>
    obtain ⟨p, rfl⟩ := hf
    obtain ⟨q, rfl⟩ := hg
    exact ⟨add p q, rfl⟩
  | mul_X f a hf =>
    obtain ⟨p, rfl⟩ := hf
    exact ⟨mul p (atom a), rfl⟩

end RationalPolynomialExpression

namespace SparseRationalPolynomial

/-- An uncollected finite multiset of rational monomials. -/
abbrev Terms (A : Type) := Multiset ((A → Nat) × ℚ)

def constant {A : Type} (c : ℚ) : Terms A := {(0, c)}

def mul {A : Type} (p q : Terms A) : Terms A :=
  p.bind (fun a => q.map (fun b => (a.1 + b.1, a.2 * b.2)))

def expand {A B : Type} (g : A → Terms B) : RationalPolynomialExpression A → Terms B
  | .constant c => constant c
  | .atom a => g a
  | .add p q => expand g p + expand g q
  | .mul p q => mul (expand g p) (expand g q)

def coefficient {A : Type} [Fintype A] (p : Terms A) (d : A → Nat) : ℚ :=
  (p.map (fun t => if t.1 = d then t.2 else 0)).sum

/-- This definition compiles: equality is tested by collecting finitely many rational coefficients. -/
def isZero {A : Type} [Fintype A] (p : Terms A) : Bool :=
  decide (∀ t ∈ p, coefficient p t.1 = 0)

noncomputable def value {A : Type} [Fintype A] (p : Terms A) : MvPolynomial A ℚ :=
  (p.map (fun t => monomial (Finsupp.equivFunOnFinite.symm t.1) t.2)).sum

theorem value_constant {A : Type} [Fintype A] (c : ℚ) : value (constant (A := A) c) = C c := by
  simp only [value, constant, Multiset.map_singleton, Multiset.sum_singleton]
  have heq : (Finsupp.equivFunOnFinite.symm (0 : A → Nat)) = 0 := by
    ext a
    rfl
  rw [heq]
  rfl

theorem value_add {A : Type} [Fintype A] (p q : Terms A) : value (p + q) = value p + value q := by
  simp only [value, Multiset.map_add, Multiset.sum_add]

theorem value_mul {A : Type} [Fintype A] (p q : Terms A) : value (mul p q) = value p * value q := by
  induction p using Multiset.induction_on with
  | empty => simp [value, mul]
  | cons a p ih =>
    have hmono : ∀ b : (A → Nat) × ℚ,
        monomial (Finsupp.equivFunOnFinite.symm (a.1 + b.1)) (a.2 * b.2) =
          monomial (Finsupp.equivFunOnFinite.symm a.1) a.2 *
            monomial (Finsupp.equivFunOnFinite.symm b.1) b.2 := by
      intro b
      rw [monomial_mul]
      have heq : Finsupp.equivFunOnFinite.symm (a.1 + b.1) =
          Finsupp.equivFunOnFinite.symm a.1 + Finsupp.equivFunOnFinite.symm b.1 := by
        ext i
        rfl
      rw [heq]
    simp only [mul, Multiset.cons_bind, value, Multiset.map_add, Multiset.sum_add,
      Multiset.map_cons, Multiset.sum_cons, Multiset.map_map, Function.comp_def] at ih ⊢
    simp_rw [hmono]
    rw [Multiset.sum_map_mul_left, ih, add_mul]

theorem value_expand {A B : Type} [Fintype B] (g : A → Terms B)
    (p : RationalPolynomialExpression A) :
    value (expand g p) = aeval (fun a => value (g a)) p.value := by
  induction p with
  | constant c => simp [expand, RationalPolynomialExpression.value, value_constant]
  | atom a => simp [expand, RationalPolynomialExpression.value]
  | add p q hp hq => simp only [expand, RationalPolynomialExpression.value,
      value_add, _root_.map_add, hp, hq]
  | mul p q hp hq => simp only [expand, RationalPolynomialExpression.value,
      value_mul, _root_.map_mul, hp, hq]

theorem coeff_value {A : Type} [Fintype A] [DecidableEq A]
    (p : Terms A) (d : A →₀ Nat) :
    (value p).coeff d = coefficient p (fun a => d a) := by
  induction p using Multiset.induction_on with
  | empty => simp [value, coefficient]
  | cons t p ih =>
    have heq : Finsupp.equivFunOnFinite.symm t.1 = d ↔ t.1 = (fun a => d a) :=
      Finsupp.equivFunOnFinite.symm_apply_eq
    simp only [value, coefficient, Multiset.map_cons, Multiset.sum_cons, coeff_add,
      coeff_monomial] at ih ⊢
    simp only [ih, heq]

theorem isZero_iff {A : Type} [Fintype A] [DecidableEq A] (p : Terms A) :
    isZero p = true ↔ value p = 0 := by
  rw [isZero, decide_eq_true_eq]
  constructor
  · intro h
    apply MvPolynomial.ext
    intro d
    rw [coeff_value, coeff_zero]
    by_cases hex : ∃ t ∈ p, t.1 = fun a => d a
    · obtain ⟨t, ht, hd⟩ := hex
      rw [← hd]
      exact h t ht
    · unfold coefficient
      apply Multiset.sum_eq_zero
      intro c hc
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
      exact if_neg (fun heq => hex ⟨t, ht, heq⟩)
  · intro h t _
    have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm t.1)) h
    simpa only [coeff_value, Finsupp.coe_equivFunOnFinite_symm, coeff_zero] using hc

end SparseRationalPolynomial

namespace MarginalVariety

open SparseRationalPolynomial

variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Exact expanded marginal coordinates, with one monomial for each latent assignment. -/
def coordinateTerms (k : Nat) (x : Assignment V) : Terms (FeatureScope (V ⊕ H) k) :=
  Finset.univ.val.map (fun h : Assignment H =>
    (fun a : FeatureScope (V ⊕ H) k =>
      if a.val ⊆ trueCoordinates (Sum.elim x h) then 1 else 0, 1))

/-- An executable decision procedure for membership in the rational marginal ideal. -/
def checkIdentity (k : Nat) (f : RationalPolynomialExpression (Assignment V)) : Bool :=
  isZero (expand (coordinateTerms (H := H) k) f)

theorem value_coordinateTerms (k : Nat) (x : Assignment V) :
    SparseRationalPolynomial.value (coordinateTerms (H := H) k x) = coordinate ℚ (H := H) k x := by
  classical
  have hmono : ∀ y : Assignment (V ⊕ H),
      monomial (Finsupp.equivFunOnFinite.symm (fun a : FeatureScope (V ⊕ H) k =>
        if a.val ⊆ trueCoordinates y then 1 else 0)) (1 : ℚ) = jointCoordinate ℚ k y := by
    intro y
    rw [monomial_eq]
    simp only [_root_.map_one, one_mul, Finsupp.prod_pow]
    apply Finset.prod_congr rfl
    intro a _
    by_cases ha : a.val ⊆ trueCoordinates y <;> simp [ha]
  simp only [SparseRationalPolynomial.value, coordinateTerms, Multiset.map_map, Function.comp_def]
  simp_rw [hmono]
  rfl

/-- Soundness and completeness, for every rational polynomial expression and hidden budget. -/
theorem checkIdentity_iff (k : Nat) (f : RationalPolynomialExpression (Assignment V)) :
    checkIdentity (H := H) k f = true ↔ f.value ∈ ideal ℚ (H := H) k := by
  rw [checkIdentity, isZero_iff, value_expand]
  simp_rw [value_coordinateTerms]
  rfl

/-- The decision procedure computes the visible intersection of the graph ideal. -/
theorem checkIdentity_iff_elimination (k : Nat)
    (f : RationalPolynomialExpression (Assignment V)) :
    checkIdentity (H := H) k f = true ↔
      MvPolynomial.map (C : ℚ →+* MvPolynomial (FeatureScope (V ⊕ H) k) ℚ) f.value ∈
        graphIdeal (H := H) k := by
  rw [checkIdentity_iff, ideal_eq_elimination]
  rfl

end MarginalVariety
end KLocality
