import KLocality.MarginalVarietyDimension
import Mathlib.RingTheory.Polynomial.Basic

namespace KLocality

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace MarginalVariety

/-- Evaluation is polynomial reduction modulo the equations `X_i = a_i`. -/
theorem evaluation_difference_mem {A S : Type*} [CommRing S]
    (a : A → S) (f : MvPolynomial A S) :
    f - C (eval a f) ∈ Ideal.span (Set.range (fun i => X i - C (a i))) := by
  let I : Ideal (MvPolynomial A S) := Ideal.span (Set.range (fun i => X i - C (a i)))
  change f - C (eval a f) ∈ I
  induction f using MvPolynomial.induction_on with
  | C s => simp
  | add f g hf hg =>
    simpa only [_root_.map_add, add_sub_add_comm] using I.add_mem hf hg
  | mul_X f i hf =>
    have hi : X i - C (a i) ∈ I := Ideal.subset_span ⟨i, rfl⟩
    have h := I.add_mem (I.mul_mem_right (X i) hf) (I.mul_mem_left (C (eval a f)) hi)
    convert h using 1
    simp only [_root_.map_mul, eval_X]
    ring

theorem evaluation_kernel_eq {A S : Type*} [CommRing S] (a : A → S) :
    RingHom.ker (eval a) = Ideal.span (Set.range (fun i => X i - C (a i))) := by
  apply le_antisymm
  · intro f hf
    have h := evaluation_difference_mem a f
    simpa only [RingHom.mem_ker.mp hf, _root_.map_zero, sub_zero] using h
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp

variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- The finite graph-equation ideal, in visible variables over the parameter ring. -/
def graphIdeal (k : Nat) :
    Ideal (MvPolynomial (Assignment V) (MvPolynomial (FeatureScope (V ⊕ H) k) ℚ)) :=
  Ideal.span (Set.range (fun x => X x - C (coordinate ℚ (H := H) k x)))

/-- **Theorem `thm:algebraic-certificate`, elimination clause.**
Intersecting the finite graph-equation ideal with the visible coefficient
subring gives exactly the homogeneous marginal ideal. -/
theorem ideal_eq_elimination (k : Nat) :
    ideal ℚ (V := V) (H := H) k =
      Ideal.comap (MvPolynomial.map (C : ℚ →+* MvPolynomial (FeatureScope (V ⊕ H) k) ℚ))
        (graphIdeal (V := V) (H := H) k) := by
  ext f
  rw [Ideal.mem_comap, graphIdeal, ← evaluation_kernel_eq, RingHom.mem_ker, mem_ideal]
  have h : eval (coordinate ℚ (H := H) k)
      (MvPolynomial.map (C : ℚ →+* MvPolynomial (FeatureScope (V ⊕ H) k) ℚ) f) =
        substitution ℚ (H := H) k f := by
    rw [eval_map]
    rfl
  rw [h]

/-- The elimination ideal has a finite generating set over the rationals. -/
theorem ideal_finitely_generated (k : Nat) : (ideal ℚ (V := V) (H := H) k).FG :=
  Ideal.fg_of_isNoetherianRing _

/-- Identity checking reduces to finitely many exact coefficients.
`MarginalIdentityDecision` implements this check and proves its correctness. -/
theorem identity_iff_substitution_coefficients_zero (k : Nat)
    (f : MvPolynomial (Assignment V) ℚ) :
    f ∈ ideal ℚ (H := H) k ↔
      ∀ d ∈ (substitution ℚ (H := H) k f).support,
        (substitution ℚ (H := H) k f).coeff d = 0 := by
  rw [mem_ideal]
  constructor
  · intro h
    simp [h]
  · intro h
    apply MvPolynomial.ext
    intro d
    by_cases hd : d ∈ (substitution ℚ (H := H) k f).support
    · simpa using h d hd
    · simpa only [mem_support_iff, not_not, coeff_zero] using hd

end MarginalVariety
end
end KLocality
