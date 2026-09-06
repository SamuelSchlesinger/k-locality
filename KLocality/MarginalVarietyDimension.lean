import KLocality.MarginalVariety
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace KLocality

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

/-- Number of Boolean monomials of degree at most `k`, including the constant. -/
def featureCount (n k : Nat) : Nat := ∑ j ∈ Finset.range (k + 1), n.choose j

theorem featureScope_card (V : Type*) [Fintype V] [DecidableEq V] (k : Nat) :
    Fintype.card (FeatureScope V k) = featureCount (Fintype.card V) k := by
  classical
  have hset : Finset.univ.filter (fun s : Finset V => s.card ≤ k) =
      (Finset.range (k + 1)).biUnion (fun j => (Finset.univ : Finset V).powersetCard j) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro hs
      exact ⟨s.card, by omega, rfl⟩
    · rintro ⟨j, hj, hcard⟩
      omega
  rw [Fintype.card_subtype, hset, Finset.card_biUnion]
  · simp [featureCount, Finset.card_powersetCard]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro s hi hj
    exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)

namespace MarginalVariety

variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Homogeneous coordinate ring of the marginal cone. -/
def CoordinateRing (k : Nat) := MvPolynomial (Assignment V) ℂ ⧸ ideal ℂ (H := H) k

instance (k : Nat) : CommRing (CoordinateRing (V := V) (H := H) k) := inferInstanceAs (CommRing (_ ⧸ _))
instance (k : Nat) : Algebra ℂ (CoordinateRing (V := V) (H := H) k) := inferInstanceAs (Algebra ℂ (_ ⧸ _))

/-- The coordinate ring embeds in a polynomial ring with one variable per feature. -/
theorem coordinateRing_trdeg_le (k : Nat) :
    Algebra.trdeg ℂ (CoordinateRing (V := V) (H := H) k) ≤
      (Fintype.card (FeatureScope (V ⊕ H) k) : Cardinal) := by
  have he := Ideal.quotientKerEquivRange (substitution ℂ (V := V) (H := H) k)
  have h := trdeg_le_of_injective
    (substitution ℂ (V := V) (H := H) k).range.val Subtype.val_injective
  rw [← he.trdeg_eq] at h
  simpa [CoordinateRing, ideal, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype] using h

/-- Projective dimension is the transcendence degree of the homogeneous
coordinate ring minus one. The preceding theorem ensures finiteness. -/
def projectiveDimension (k : Nat) : Nat :=
  (Algebra.trdeg ℂ (CoordinateRing (V := V) (H := H) k)).toNat - 1

/-- **Theorem `thm:algebraic-certificate`, dimension clause.** -/
theorem projectiveDimension_le (n k ell : Nat) :
    projectiveDimension (V := Fin n) (H := Fin ell) k ≤ featureCount (n + ell) k - 1 := by
  have h := Cardinal.toNat_le_toNat
    (coordinateRing_trdeg_le (V := Fin n) (H := Fin ell) k) (by simp)
  simp only [Cardinal.toNat_natCast, featureScope_card, Fintype.card_sum, Fintype.card_fin] at h
  exact Nat.sub_le_sub_right h 1

/-- Below the parameter-count threshold the rational substitution has a nonzero kernel. -/
theorem exists_rational_identity (n k ell : Nat) (hcount : featureCount (n + ell) k < 2 ^ n) :
    ∃ f : MvPolynomial (BitVec n) ℚ, f ∈ ideal ℚ (H := Fin ell) k ∧ f ≠ 0 := by
  have hnot : ¬AlgebraicIndependent ℚ (coordinate ℚ (V := Fin n) (H := Fin ell) k) := by
    intro hind
    have h := hind.cardinalMk_le_trdeg
    have hnat : 2 ^ n ≤ featureCount (n + ell) k := by
      have h' : ((2 ^ n : Nat) : Cardinal) ≤ (featureCount (n + ell) k : Cardinal) := by
        simpa [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fun,
        featureScope_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool,
        Assignment] using h
      exact_mod_cast h'
    omega
  rw [algebraicIndependent_iff] at hnot
  push_neg at hnot
  exact hnot

theorem exists_homogeneous_rational_identity (n k ell : Nat)
    (hcount : featureCount (n + ell) k < 2 ^ n) :
    ∃ degree, ∃ f : MvPolynomial (BitVec n) ℚ,
      f.IsHomogeneous degree ∧ f ∈ ideal ℚ (H := Fin ell) k ∧ f ≠ 0 := by
  obtain ⟨f, hf, hne⟩ := exists_rational_identity n k ell hcount
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hne
  refine ⟨d.degree, homogeneousComponent d.degree f,
    homogeneousComponent_isHomogeneous _ _, homogeneousComponent_mem_ideal k hf _, ?_⟩
  intro hzero
  have h := congrArg (coeff d) hzero
  simp only [coeff_homogeneousComponent, coeff_zero] at h
  exact hd h

/-- Clear denominators using finite polynomial induction, rather than an
assumption about rational or integer algebraic sets. -/
theorem clear_denominators {A : Type*} (f : MvPolynomial A ℚ) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ g : MvPolynomial A ℤ,
      MvPolynomial.map (Int.castRingHom ℚ) g = C (c : ℚ) * f := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    refine ⟨r.den, by exact_mod_cast r.den_nz, C r.num, ?_⟩
    simp only [MvPolynomial.map_C, Int.coe_castRingHom, Int.cast_natCast, ← _root_.map_mul]
    congr 1
    have h := (div_eq_iff (by exact_mod_cast r.den_nz : (r.den : ℚ) ≠ 0)).mp r.num_div_den
    simpa only [mul_comm] using h
  | add f g hf hg =>
    obtain ⟨c, hc, p, hp⟩ := hf
    obtain ⟨d, hd, q, hq⟩ := hg
    refine ⟨c * d, mul_ne_zero hc hd, C d * p + C c * q, ?_⟩
    simp only [_root_.map_add, _root_.map_mul, MvPolynomial.map_C,
      Int.coe_castRingHom, hp, hq, Int.cast_mul]
    ring
  | mul_X f a hf =>
    obtain ⟨c, hc, p, hp⟩ := hf
    refine ⟨c, hc, p * X a, ?_⟩
    simp only [_root_.map_mul, hp, MvPolynomial.map_X, mul_assoc]

/-- **Theorem `thm:algebraic-certificate`, integer-certificate clause.** -/
theorem exists_homogeneous_integer_identity (n k ell : Nat)
    (hcount : featureCount (n + ell) k < 2 ^ n) :
    ∃ degree, ∃ f : MvPolynomial (BitVec n) ℤ,
      f.IsHomogeneous degree ∧ f ∈ ideal ℤ (H := Fin ell) k ∧ f ≠ 0 := by
  obtain ⟨degree, f, hhom, hker, hne⟩ := exists_homogeneous_rational_identity n k ell hcount
  obtain ⟨c, hc, g, hg⟩ := clear_denominators f
  have hcast : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hmapne : MvPolynomial.map (Int.castRingHom ℚ) g ≠ 0 := by
    rw [hg]
    exact mul_ne_zero (by simpa using hcast) hne
  refine ⟨degree, g, ?_, ?_, fun h => hmapne (by simp [h])⟩
  · apply IsHomogeneous.of_map (f := Int.castRingHom ℚ) Int.cast_injective
    rw [hg]
    exact hhom.C_mul _
  · rw [mem_ideal]
    apply (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
    rw [map_substitution, hg]
    change substitution ℚ (H := Fin ell) k (C (c : ℚ) * f) = _
    rw [_root_.map_mul, (mem_ideal ℚ k f).mp hker, mul_zero, _root_.map_zero]

end MarginalVariety
end
end KLocality
