import KLocality.MarginalVarietyElimination
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace KLocality

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace MarginalVariety

/-- Homogeneous polynomial evaluation transforms by the expected scalar power. -/
theorem eval_homogeneous_scale {A R : Type*} [CommRing R]
    {f : MvPolynomial A R} {degree : Nat} (hf : f.IsHomogeneous degree)
    (c : R) (z : A → R) :
    eval (c • z) f = c ^ degree * eval z f := by
  classical
  simp only [eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree : ∑ i ∈ d.support, d i = degree := by
    simpa [MvPolynomial.IsHomogeneous, Finsupp.weight_apply, Finsupp.sum] using
      hf (mem_support_iff.mp hd)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdegree]
  ring

variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- The homogeneous marginal ideal is prime, as the target polynomial ring is a domain. -/
instance ideal_isPrime (k : Nat) : (ideal ℂ (V := V) (H := H) k).IsPrime :=
  RingHom.ker_isPrime (substitution ℂ (V := V) (H := H) k).toRingHom

instance coordinateRing_isDomain (k : Nat) : IsDomain (CoordinateRing (V := V) (H := H) k) :=
  inferInstanceAs (IsDomain (_ ⧸ _))

theorem smul_mem_cone (k : Nat) {z : Assignment V → ℂ}
    (hz : z ∈ cone (H := H) k) (c : ℂ) : c • z ∈ cone (H := H) k := by
  intro f hf
  change eval (c • z) f = 0
  rw [← sum_homogeneousComponent f, _root_.map_sum]
  apply Finset.sum_eq_zero
  intro degree _
  rw [eval_homogeneous_scale (homogeneousComponent_isHomogeneous _ _),
    show eval z (homogeneousComponent degree f) = 0 from
      hz _ (homogeneousComponent_mem_ideal k hf degree), mul_zero]

/-- The actual projective marginal variety, represented by its homogeneous cone. -/
def projectiveVariety (k : Nat) : Set (Projectivization ℂ (Assignment V → ℂ)) :=
  {p | p.rep ∈ cone (H := H) k}

/-- Membership is independent of the representative chosen by `Projectivization.rep`. -/
theorem mk_mem_projectiveVariety_iff (k : Nat) (z : Assignment V → ℂ) (hz : z ≠ 0) :
    Projectivization.mk ℂ z hz ∈ projectiveVariety (H := H) k ↔ z ∈ cone (H := H) k := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ z hz
  change (Projectivization.mk ℂ z hz).rep ∈ cone (H := H) k ↔ _
  rw [← ha]
  constructor
  · intro h
    have h' := smul_mem_cone k h (↑a⁻¹ : ℂ)
    simpa only [← Units.smul_def, inv_smul_smul] using h'
  · exact fun h => smul_mem_cone k h (a : ℂ)

omit [Fintype V] [DecidableEq V] in
theorem eval_rep_eq_zero_iff {f : MvPolynomial (Assignment V) ℂ} {degree : Nat}
    (hf : f.IsHomogeneous degree) (z : Assignment V → ℂ) (hz : z ≠ 0) :
    eval (Projectivization.mk ℂ z hz).rep f = 0 ↔ eval z f = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ z hz
  rw [← ha]
  change eval ((a : ℂ) • z) f = 0 ↔ _
  rw [eval_homogeneous_scale hf]
  simp only [mul_eq_zero, pow_ne_zero degree a.ne_zero, false_or]

/-- The projective image discards zero vectors, where projective coordinates are undefined. -/
def projectiveParameterImage (k : Nat) : Set (Projectivization ℂ (Assignment V → ℂ)) :=
  {p | ∃ (z : Assignment V → ℂ) (hz : z ≠ 0),
    z ∈ parameterImage (H := H) k ∧ Projectivization.mk ℂ z hz = p}

/-- Projective image of the displayed map without its auxiliary scale.
The empty parameter is ignored by `unscaledCoordinate`. -/
def unscaledProjectiveParameterImage (k : Nat) : Set (Projectivization ℂ (Assignment V → ℂ)) :=
  {p | ∃ (t : FeatureScope (V ⊕ H) k → ℂ), (∀ a, t a ≠ 0) ∧
    ∃ hz : (fun x => eval t (unscaledCoordinate ℂ (H := H) k x)) ≠ 0,
      Projectivization.mk ℂ (fun x => eval t (unscaledCoordinate ℂ (H := H) k x)) hz = p}

theorem eval_coordinate_eq_scale_smul (k : Nat) (t : FeatureScope (V ⊕ H) k → ℂ) :
    (fun x => eval t (coordinate ℂ (H := H) k x)) =
      t (FeaturePolynomial.emptyScope (V ⊕ H) k) •
        (fun x => eval t (unscaledCoordinate ℂ (H := H) k x)) := by
  funext x
  simp only [coordinate_eq_scale_mul, _root_.map_mul, eval_X, Pi.smul_apply, smul_eq_mul]

/-- The freely varying scale parameter does not change the projective image. -/
theorem projectiveParameterImage_eq_unscaled (k : Nat) :
    projectiveParameterImage (V := V) (H := H) k =
      unscaledProjectiveParameterImage (V := V) (H := H) k := by
  ext p
  constructor
  · rintro ⟨z, hz, ⟨t, ht, rfl⟩, rfl⟩
    have hq : (fun x => eval t (unscaledCoordinate ℂ (H := H) k x)) ≠ 0 := by
      intro h
      apply hz
      rw [eval_coordinate_eq_scale_smul, h, smul_zero]
    refine ⟨t, ht, hq, ?_⟩
    symm
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      ⟨t (FeaturePolynomial.emptyScope (V ⊕ H) k), (eval_coordinate_eq_scale_smul k t).symm⟩
  · rintro ⟨t, ht, hz, rfl⟩
    have hp : (fun x => eval t (coordinate ℂ (H := H) k x)) ≠ 0 := by
      rw [eval_coordinate_eq_scale_smul]
      exact smul_ne_zero (ht _) hz
    refine ⟨_, hp, ⟨t, ht, rfl⟩, ?_⟩
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      ⟨t (FeaturePolynomial.emptyScope (V ⊕ H) k), (eval_coordinate_eq_scale_smul k t).symm⟩

/-- Zariski closure in projective space: all homogeneous equations vanishing on the set. -/
def projectiveZariskiClosure (S : Set (Projectivization ℂ (Assignment V → ℂ))) :
    Set (Projectivization ℂ (Assignment V → ℂ)) :=
  {p | ∀ (degree : Nat) (f : MvPolynomial (Assignment V) ℂ), f.IsHomogeneous degree →
    (∀ q ∈ S, eval q.rep f = 0) → eval p.rep f = 0}

theorem exists_nonzero_parameterImage (k : Nat) :
    ∃ z : Assignment V → ℂ, z ∈ parameterImage (H := H) k ∧ z ≠ 0 := by
  classical
  let z : Assignment V → ℂ := fun x => eval (fun _ => 1) (coordinate ℂ (H := H) k x)
  have hvalue : ∀ x, z x = (Fintype.card (Assignment H) : ℂ) := by
    intro x
    simp [z, coordinate, jointCoordinate, apply_ite]
  refine ⟨z, ⟨fun _ => 1, fun _ => one_ne_zero, rfl⟩, ?_⟩
  intro hz
  have h := congrFun hz (fun _ => false)
  rw [hvalue] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero :
    (Fintype.card (Assignment H) : ℂ) ≠ 0) h

theorem homogeneous_mem_ideal_iff_vanishes_on_projectiveImage (k : Nat)
    {f : MvPolynomial (Assignment V) ℂ} {degree : Nat} (hf : f.IsHomogeneous degree) :
    f ∈ ideal ℂ (H := H) k ↔
      ∀ p ∈ projectiveParameterImage (H := H) k, eval p.rep f = 0 := by
  constructor
  · intro h p hp
    obtain ⟨z, hz, himage, rfl⟩ := hp
    apply (eval_rep_eq_zero_iff hf z hz).mpr
    rw [ideal_eq_vanishingIdeal] at h
    exact h z himage
  · intro h
    have hzero : eval (0 : Assignment V → ℂ) f = 0 := by
      obtain ⟨z, himage, hz⟩ := exists_nonzero_parameterImage (V := V) (H := H) k
      have heval := (eval_rep_eq_zero_iff hf z hz).mp (h _ ⟨z, hz, himage, rfl⟩)
      have hscale := eval_homogeneous_scale hf 0 z
      simpa only [zero_smul, heval, mul_zero] using hscale
    rw [ideal_eq_vanishingIdeal]
    intro z hz
    change eval z f = 0
    by_cases hne : z = 0
    · simpa only [hne] using hzero
    · exact (eval_rep_eq_zero_iff hf z hne).mp (h _ ⟨z, hne, hz, rfl⟩)

/-- The variety is precisely the complex projective Zariski closure in the manuscript. -/
theorem projectiveVariety_eq_zariskiClosure (k : Nat) :
    projectiveVariety (V := V) (H := H) k =
      projectiveZariskiClosure (projectiveParameterImage (V := V) (H := H) k) := by
  ext p
  constructor
  · intro hp degree f hf hvanish
    exact hp f ((homogeneous_mem_ideal_iff_vanishes_on_projectiveImage k hf).mpr hvanish)
  · intro hp f hf
    change eval p.rep f = 0
    rw [← sum_homogeneousComponent f, _root_.map_sum]
    apply Finset.sum_eq_zero
    intro degree _
    exact hp degree (homogeneousComponent degree f) (homogeneousComponent_isHomogeneous _ _)
      ((homogeneous_mem_ideal_iff_vanishes_on_projectiveImage k
        (homogeneousComponent_isHomogeneous _ _)).mp (homogeneousComponent_mem_ideal k hf degree))

theorem parameterImage_subset_cone (k : Nat) :
    parameterImage (V := V) (H := H) k ⊆ cone (H := H) k := by
  rw [cone, ideal_eq_vanishingIdeal]
  exact zeroLocus_vanishingIdeal_le _

/-- The cone's vanishing ideal is exactly the substitution kernel. -/
theorem vanishingIdeal_cone (k : Nat) :
    vanishingIdeal ℂ (cone (V := V) (H := H) k) = ideal ℂ (H := H) k := by
  apply le_antisymm
  · rw [ideal_eq_vanishingIdeal]
    exact vanishingIdeal_anti_mono (parameterImage_subset_cone k)
  · exact le_vanishingIdeal_zeroLocus _

theorem homogeneous_mem_ideal_iff_vanishes_on_variety (k : Nat)
    {f : MvPolynomial (Assignment V) ℂ} {degree : Nat} (hf : f.IsHomogeneous degree) :
    f ∈ ideal ℂ (H := H) k ↔
      ∀ p ∈ projectiveVariety (H := H) k, eval p.rep f = 0 := by
  constructor
  · exact fun h _ hp => hp f h
  · intro h
    apply (homogeneous_mem_ideal_iff_vanishes_on_projectiveImage k hf).mpr
    intro p hp
    obtain ⟨z, hz, himage, rfl⟩ := hp
    exact h _ ((mk_mem_projectiveVariety_iff k z hz).mpr (parameterImage_subset_cone k himage))

def probabilityVector (p : Distribution (Assignment V)) : Assignment V → ℂ :=
  fun x => ((p x).toReal : ℂ)

omit [Fintype V] [DecidableEq V] in
theorem probabilityVector_ne_zero (p : Distribution (Assignment V)) :
    probabilityVector p ≠ 0 := by
  obtain ⟨x, hx⟩ := p.support_nonempty
  have hpos : 0 < (p x).toReal := ENNReal.toReal_pos
    ((PMF.mem_support_iff p x).mp hx) (p.apply_ne_top x)
  intro h
  have hz := congrFun h x
  simp only [probabilityVector, Pi.zero_apply, Complex.ofReal_eq_zero] at hz
  exact hpos.ne' hz

def projectiveDistribution (p : Distribution (Assignment V)) :
    Projectivization ℂ (Assignment V → ℂ) :=
  Projectivization.mk ℂ (probabilityVector p) (probabilityVector_ne_zero p)

/-- The manuscript's projective containment, including all boundary localizations. -/
theorem projectiveDistribution_mem_of_localizationComplexity_le {k budget : Nat}
    (hk : 2 ≤ k) (p : Distribution (Assignment V))
    (hbudget : localizationComplexity k V p ≤ budget) :
    projectiveDistribution p ∈ projectiveVariety (H := Fin budget) k :=
  (mk_mem_projectiveVariety_iff k _ _).mpr
    (mem_cone_of_localizationComplexity_le hk p hbudget)

/-- The certificate implication stated entirely on the projective variety. -/
theorem localizationComplexity_gt_of_homogeneous_polynomial {k budget degree : Nat}
    (hk : 2 ≤ k) (p : Distribution (Assignment V))
    (f : MvPolynomial (Assignment V) ℂ) (hf : f.IsHomogeneous degree)
    (hvanish : ∀ z ∈ projectiveVariety (H := Fin budget) k, eval z.rep f = 0)
    (hdetect : eval (probabilityVector p) f ≠ 0) :
    budget < localizationComplexity k V p :=
  localizationComplexity_gt_of_polynomial hk p f
    ((homogeneous_mem_ideal_iff_vanishes_on_variety k hf).mpr hvanish) hdetect

/-- The integer certificate exists in the actual projective vanishing ideal. -/
theorem exists_homogeneous_integer_certificate (n k ell : Nat)
    (hcount : featureCount (n + ell) k < 2 ^ n) :
    ∃ degree, ∃ f : MvPolynomial (BitVec n) ℤ,
      f.IsHomogeneous degree ∧ f ≠ 0 ∧
        ∀ z ∈ projectiveVariety (V := Fin n) (H := Fin ell) k,
          eval z.rep (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  obtain ⟨degree, f, hf, hker, hne⟩ := exists_homogeneous_integer_identity n k ell hcount
  refine ⟨degree, f, hf, hne, ?_⟩
  apply (homogeneous_mem_ideal_iff_vanishes_on_variety k (hf.map (Int.castRingHom ℂ))).mp
  exact (map_mem_ideal_iff (Int.castRingHom ℂ) Int.cast_injective k f).mpr hker

end MarginalVariety
end
end KLocality
