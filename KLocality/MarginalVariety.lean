import KLocality.LatentPadding
import KLocality.MarginalTradeCertificate
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Nullstellensatz

namespace KLocality

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace MarginalVariety

variable (R : Type*) [CommRing R]
variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Toric coordinates including the empty feature, which is the projective scale. -/
def jointCoordinate (k : Nat) (y : Assignment V) : MvPolynomial (FeatureScope V k) R :=
  ∏ a : FeatureScope V k, if a.val ⊆ trueCoordinates y then X a else 1

/-- The manuscript's toric monomial, using only nonconstant features. -/
def unscaledJointCoordinate (k : Nat) (y : Assignment V) :
    MvPolynomial (FeatureScope V k) R :=
  ∏ a ∈ Finset.univ.erase (FeaturePolynomial.emptyScope V k),
    if a.val ⊆ trueCoordinates y then X a else 1

theorem jointCoordinate_eq_scale_mul (k : Nat) (y : Assignment V) :
    jointCoordinate R k y = X (FeaturePolynomial.emptyScope V k) *
      unscaledJointCoordinate R k y := by
  classical
  simpa only [jointCoordinate, unscaledJointCoordinate, FeaturePolynomial.emptyScope,
    Finset.empty_subset, if_true] using
    (Finset.mul_prod_erase Finset.univ
      (fun a : FeatureScope V k => if a.val ⊆ trueCoordinates y then (X a : MvPolynomial _ R) else 1)
      (Finset.mem_univ (FeaturePolynomial.emptyScope V k))).symm

/-- The polynomial marginal map, before normalization. -/
def coordinate (k : Nat) (x : Assignment V) : MvPolynomial (FeatureScope (V ⊕ H) k) R :=
  ∑ h : Assignment H, jointCoordinate R k (Sum.elim x h)

def unscaledCoordinate (k : Nat) (x : Assignment V) :
    MvPolynomial (FeatureScope (V ⊕ H) k) R :=
  ∑ h : Assignment H, unscaledJointCoordinate R k (Sum.elim x h)

/-- Including the empty feature is exactly the extra scale variable `s` in
the manuscript's elimination equations `p_x - s*q_x(t)`. -/
theorem coordinate_eq_scale_mul (k : Nat) (x : Assignment V) :
    coordinate R (H := H) k x = X (FeaturePolynomial.emptyScope (V ⊕ H) k) *
      unscaledCoordinate R (H := H) k x := by
  simp only [coordinate, jointCoordinate_eq_scale_mul, unscaledCoordinate, Finset.mul_sum]

/-- Substitution into the marginal parametrization. Its kernel is the cone ideal. -/
def substitution (k : Nat) :
    MvPolynomial (Assignment V) R →ₐ[R] MvPolynomial (FeatureScope (V ⊕ H) k) R :=
  aeval (coordinate R (H := H) k)

def ideal (k : Nat) : Ideal (MvPolynomial (Assignment V) R) :=
  RingHom.ker (substitution R (V := V) (H := H) k).toRingHom

@[simp] theorem mem_ideal (k : Nat) (f : MvPolynomial (Assignment V) R) :
    f ∈ ideal R (V := V) (H := H) k ↔ substitution R (H := H) k f = 0 := Iff.rfl

variable {R}

theorem eval_substitution (k : Nat) (f : MvPolynomial (Assignment V) R)
    (t : FeatureScope (V ⊕ H) k → R) :
    eval t (substitution R (H := H) k f) =
      eval (fun x => eval t (coordinate R (H := H) k x)) f := by
  exact MvPolynomial.comp_aeval_apply (coordinate R (H := H) k) (aeval t) f

/-- The algebraic cone over the projective marginal variety. -/
def cone (k : Nat) : Set (Assignment V → ℂ) :=
  zeroLocus ℂ (ideal ℂ (V := V) (H := H) k)

theorem eval_joint_exp (k : Nat) (theta : FeaturePolynomial V k) (y : Assignment V) :
    eval (fun a => Real.exp (theta a)) (jointCoordinate ℝ k y) =
      Real.exp (theta.eval y) := by
  classical
  simp only [jointCoordinate, _root_.map_prod]
  have hterm : ∀ a : FeatureScope V k,
      eval (fun a => Real.exp (theta a)) (if a.val ⊆ trueCoordinates y then X a else 1) =
        Real.exp (theta a * monomialValue a.val y) := by
    intro a
    by_cases h : a.val ⊆ trueCoordinates y <;> simp [h, monomialValue]
  simp_rw [hterm]
  rw [← Real.exp_sum]
  rfl

theorem eval_joint_exp_complex (k : Nat) (theta : FeaturePolynomial V k) (y : Assignment V) :
    eval (fun a => (Real.exp (theta a) : ℂ)) (jointCoordinate ℂ k y) =
      (Real.exp (theta.eval y) : ℂ) := by
  classical
  have h := congrArg Complex.ofReal (eval_joint_exp k theta y)
  simpa [jointCoordinate, apply_ite, Complex.ofReal_prod] using h

/-- Unnormalized positive Gibbs weights converge to the calibrated face--Gibbs law. -/
theorem faceGibbs_toric_limit (k : Nat) (p : Distribution (Assignment V))
    (hp : IsFaceGibbs k p) :
    ∃ t : ℝ → FeatureScope V k → ℂ,
      Tendsto (fun r y => eval (t r) (jointCoordinate ℂ k y)) atTop
        (𝓝 (fun y => ((p y).toReal : ℂ))) := by
  obtain ⟨⟨energy, hnonneg, hzero⟩, theta, hlog⟩ := hp
  refine ⟨fun r a => (Real.exp (theta a - r * energy a) : ℂ), ?_⟩
  apply tendsto_pi_nhds.mpr
  intro y
  have heval : ∀ r : ℝ,
      eval (fun a => (Real.exp (theta a - r * energy a) : ℂ)) (jointCoordinate ℂ k y) =
        (Real.exp (theta.eval y - r * energy.eval y) : ℂ) := by
    intro r
    have h := eval_joint_exp_complex k (theta - r • energy) y
    have hevalpoly : (theta - r • energy).eval y = theta.eval y - r * energy.eval y := by
      simp [FeaturePolynomial.eval, sub_mul, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hevalpoly] using h
  simp_rw [heval]
  apply Complex.continuous_ofReal.continuousAt.tendsto.comp
  by_cases hy : y ∈ p.support
  · have he : energy.eval y = 0 := (hzero y).mpr hy
    have hpval : 0 < (p y).toReal := ENNReal.toReal_pos
      ((PMF.mem_support_iff p y).mp hy) (p.apply_ne_top y)
    simp only [he, mul_zero, sub_zero, ← hlog y hy, Real.exp_log hpval]
    exact tendsto_const_nhds
  · have he : 0 < energy.eval y := lt_of_le_of_ne (hnonneg y)
      (fun h => hy ((hzero y).mp h.symm))
    have hpzero : p y = 0 := (p.apply_eq_zero_iff y).mpr hy
    rw [hpzero, ENNReal.toReal_zero]
    apply Real.tendsto_exp_atBot.comp
    simpa only [sub_eq_add_neg, Function.comp_def] using
      tendsto_atBot_add_const_left atTop (theta.eval y)
        (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const he))

/-- Every boundary localization belongs to the same marginal cone as the positive models. -/
theorem localization_mem_cone (k : Nat) (p : Distribution (Assignment V))
    (loc : KLocalization k V H p) :
    (fun x => ((p x).toReal : ℂ)) ∈ cone (H := H) k := by
  obtain ⟨t, ht⟩ := faceGibbs_toric_limit k loc.lifted
    ((isKLocalMarginal_iff_isFaceGibbs k loc.lifted).mp loc.kLocal)
  have hmarg : ∀ x, (∑ h : Assignment H,
      ((loc.lifted (Sum.elim x h)).toReal : ℂ)) = ((p x).toReal : ℂ) := by
    intro x
    have h := map_projectObs_apply_toReal loc.lifted x
    rw [loc.marginal] at h
    exact_mod_cast h.symm
  have hlimit : Tendsto (fun r x => eval (t r) (coordinate ℂ (H := H) k x)) atTop
      (𝓝 (fun x => ((p x).toReal : ℂ))) := by
    apply tendsto_pi_nhds.mpr
    intro x
    simp only [coordinate, _root_.map_sum]
    rw [← hmarg x]
    exact tendsto_finset_sum Finset.univ (fun h _ => (tendsto_pi_nhds.mp ht) (Sum.elim x h))
  intro f hf
  have hzero : ∀ r, eval (fun x => eval (t r) (coordinate ℂ (H := H) k x)) f = 0 := by
    intro r
    rw [← eval_substitution, (mem_ideal ℂ k f).mp hf, _root_.map_zero]
  have hlim := f.continuous_eval.continuousAt.tendsto.comp hlimit
  simp only [Function.comp_def, hzero] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- The empty feature measures the degree in the cone's scale coordinate. -/
def scaleWeight (k : Nat) (a : FeatureScope V k) : Nat := if a.val = ∅ then 1 else 0

theorem jointCoordinate_weighted (k : Nat) (y : Assignment V) :
    (jointCoordinate R k y).IsWeightedHomogeneous (scaleWeight k) 1 := by
  classical
  let deg : FeatureScope V k → Nat :=
    fun a => if a.val ⊆ trueCoordinates y then scaleWeight k a else 0
  have hsum : ∑ a : FeatureScope V k, deg a = 1 := by
    rw [Finset.sum_eq_single (FeaturePolynomial.emptyScope V k)]
    · simp [deg, scaleWeight, FeaturePolynomial.emptyScope]
    · intro a _ ha
      have hempty : a.val ≠ ∅ := by
        intro h
        exact ha (Subtype.ext h)
      simp [deg, scaleWeight, hempty]
    · simp
  unfold jointCoordinate
  rw [← hsum]
  apply IsWeightedHomogeneous.prod
  intro a _
  dsimp [deg]
  split_ifs
  · exact isWeightedHomogeneous_X R (scaleWeight k) a
  · exact isWeightedHomogeneous_one _ _

theorem coordinate_weighted (k : Nat) (x : Assignment V) :
    (coordinate R (H := H) k x).IsWeightedHomogeneous (scaleWeight k) 1 := by
  apply IsWeightedHomogeneous.sum
  intro h _
  exact jointCoordinate_weighted k (Sum.elim x h)

/-- Substitution by forms of weighted degree one preserves homogeneous degree. -/
theorem aeval_weighted {A C : Type*} (w : C → Nat)
    {f : MvPolynomial A R} {n : Nat} (hf : f.IsHomogeneous n)
    (g : A → MvPolynomial C R) (hg : ∀ a, (g a).IsWeightedHomogeneous w 1) :
    (aeval g f).IsWeightedHomogeneous w n := by
  change (eval₂ MvPolynomial.C g f).IsWeightedHomogeneous w n
  apply IsWeightedHomogeneous.sum
  intro d hd
  have hdegree := hf (mem_support_iff.mp hd)
  have hprod : (∏ a ∈ d.support, g a ^ d a).IsWeightedHomogeneous w n := by
    have h := IsWeightedHomogeneous.prod d.support (fun a => g a ^ d a) (fun a => d a)
      (fun a _ => by simpa using (hg a).pow (d a))
    convert h using 1
    simpa [MvPolynomial.IsHomogeneous, Finsupp.weight_apply, Finsupp.sum] using hdegree.symm
  simpa using (isWeightedHomogeneous_C w (f.coeff d)).mul hprod

theorem substitution_homogeneous (k : Nat) {f : MvPolynomial (Assignment V) R} {n : Nat}
    (hf : f.IsHomogeneous n) :
    (substitution R (H := H) k f).IsWeightedHomogeneous (scaleWeight k) n :=
  aeval_weighted _ hf _ (coordinate_weighted k)

/-- Homogeneous components of a marginal identity are again marginal identities. -/
theorem substitution_homogeneousComponent (k : Nat) (f : MvPolynomial (Assignment V) R)
    (n : Nat) :
    weightedHomogeneousComponent (scaleWeight k) n (substitution R (H := H) k f) =
      substitution R (H := H) k (homogeneousComponent n f) := by
  classical
  nth_rw 1 [← sum_homogeneousComponent f]
  simp only [_root_.map_sum]
  rw [Finset.sum_eq_single n]
  · exact (substitution_homogeneous (H := H) k (homogeneousComponent_isHomogeneous n f)).weightedHomogeneousComponent_same
  · intro i _ hi
    exact (substitution_homogeneous (H := H) k (homogeneousComponent_isHomogeneous i f)).weightedHomogeneousComponent_ne n (Ne.symm hi)
  · intro hn
    have hdeg : f.totalDegree < n := by simpa using hn
    simp only [homogeneousComponent_eq_zero n f hdeg, _root_.map_zero]

theorem homogeneousComponent_mem_ideal (k : Nat) {f : MvPolynomial (Assignment V) R}
    (hf : f ∈ ideal R (H := H) k) (n : Nat) :
    homogeneousComponent n f ∈ ideal R (H := H) k := by
  rw [mem_ideal, ← substitution_homogeneousComponent, (mem_ideal R k f).mp hf]
  exact (weightedHomogeneousComponent (R := R) (scaleWeight (V := V ⊕ H) k) n).map_zero

theorem map_jointCoordinate {S : Type*} [CommRing S] (f : R →+* S)
    (k : Nat) (y : Assignment V) :
    MvPolynomial.map f (jointCoordinate R k y) = jointCoordinate S k y := by
  classical
  simp [jointCoordinate, apply_ite]

theorem map_coordinate {S : Type*} [CommRing S] (f : R →+* S)
    (k : Nat) (x : Assignment V) :
    MvPolynomial.map f (coordinate R (H := H) k x) = coordinate S (H := H) k x := by
  simp only [coordinate, _root_.map_sum, map_jointCoordinate]

theorem map_substitution {S : Type*} [CommRing S] (f : R →+* S)
    (k : Nat) (p : MvPolynomial (Assignment V) R) :
    MvPolynomial.map f (substitution R (H := H) k p) =
      substitution S (H := H) k (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [substitution, algebraMap_eq]
  | add p q hp hq => simp only [_root_.map_add, hp, hq]
  | mul_X p x hp =>
    change MvPolynomial.map f (aeval (coordinate R (H := H) k) p) =
      aeval (coordinate S (H := H) k) (MvPolynomial.map f p) at hp
    simp only [substitution, _root_.map_mul, aeval_X, MvPolynomial.map_X, map_coordinate, hp]

/-- Coefficient extension to an injective ring preserves and reflects every identity. -/
theorem map_mem_ideal_iff {S : Type*} [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (k : Nat) (p : MvPolynomial (Assignment V) R) :
    MvPolynomial.map f p ∈ ideal S (H := H) k ↔ p ∈ ideal R (H := H) k := by
  rw [mem_ideal, mem_ideal, ← map_substitution]
  exact (MvPolynomial.map_injective f hf).eq_iff' (by simp)

/-- The complex torus, including its freely varying scale parameter. -/
def parameterImage (k : Nat) : Set (Assignment V → ℂ) :=
  {p | ∃ t : FeatureScope (V ⊕ H) k → ℂ,
    (∀ a, t a ≠ 0) ∧ p = fun x => eval t (coordinate ℂ (H := H) k x)}

/-- The substitution kernel is exactly the vanishing ideal of the torus image;
allowing zero parameters requires no saturation. -/
theorem ideal_eq_vanishingIdeal (k : Nat) :
    ideal ℂ (V := V) (H := H) k = vanishingIdeal ℂ (parameterImage (V := V) (H := H) k) := by
  ext f
  constructor
  · intro hf p hp
    obtain ⟨t, _, rfl⟩ := hp
    change eval _ f = 0
    rw [← eval_substitution, (mem_ideal ℂ k f).mp hf, _root_.map_zero]
  · intro hf
    rw [mem_ideal]
    apply MvPolynomial.funext_set (fun _ => ({0} : Set ℂ)ᶜ)
      (fun _ => by
        have h := Set.infinite_univ.diff (Set.finite_singleton (0 : ℂ))
        convert h using 1
        ext z
        simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_univ, true_and])
    intro t ht
    rw [_root_.map_zero, eval_substitution]
    exact hf _ ⟨t, (fun a => by simpa using ht a (Set.mem_univ a)), rfl⟩

/-- Literal Zariski closure of the parametrized cone. -/
theorem cone_eq_zariskiClosure (k : Nat) :
    cone (V := V) (H := H) k =
      zeroLocus ℂ (vanishingIdeal ℂ (parameterImage (V := V) (H := H) k)) := by
  rw [cone, ideal_eq_vanishingIdeal]

/-- **Theorem `thm:algebraic-certificate`, containment clause.** -/
theorem mem_cone_of_localizationComplexity_le {k budget : Nat} (hk : 2 ≤ k)
    (p : Distribution (Assignment V)) (hbudget : localizationComplexity k V p ≤ budget) :
    (fun x => ((p x).toReal : ℂ)) ∈ cone (H := Fin budget) k := by
  have hloc := hasKLocalization_padLatent (by omega : 1 ≤ k) hbudget
    (localizationComplexity_spec k V p (kLocalization_exists p hk))
  obtain ⟨loc⟩ := hloc
  exact localization_mem_cone k p loc

/-- A detected polynomial from the full marginal ideal rules out the hidden budget. -/
theorem localizationComplexity_gt_of_polynomial {k budget : Nat} (hk : 2 ≤ k)
    (p : Distribution (Assignment V)) (f : MvPolynomial (Assignment V) ℂ)
    (hf : f ∈ ideal ℂ (H := Fin budget) k)
    (hdetect : eval (fun x => ((p x).toReal : ℂ)) f ≠ 0) :
    budget < localizationComplexity k V p := by
  by_contra h
  have hp := mem_cone_of_localizationComplexity_le hk p (Nat.le_of_not_gt h)
  exact hdetect (hp f hf)

end MarginalVariety
end
end KLocality
