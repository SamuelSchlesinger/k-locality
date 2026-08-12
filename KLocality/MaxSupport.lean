import KLocality.Canonical

namespace KLocality

open scoped BigOperators

universe u

/-!
# Maximal support of entropy maximizers

This module formalizes Lemma `lem:max-support`.  Affine equality fibers are
convex, and convexity is the only property of the fiber used by the proof, so
the main theorem is stated for an arbitrary mixture-closed family of finite
PMFs.
-/

/-- The convex mixture `(1-t) p + t q` of two finite PMFs. -/
noncomputable def mixDistribution
    {α : Type u} [Fintype α]
    (t : NNReal) (ht : t ≤ 1) (p q : Distribution α) : Distribution α := by
  classical
  refine PMF.ofFintype
    (fun a => ((1 - t : NNReal) : ENNReal) * p a + (t : ENNReal) * q a) ?_
  have hp : ∑ a, p a = (1 : ENNReal) := by
    simpa only [tsum_fintype] using p.tsum_coe
  have hq : ∑ a, q a = (1 : ENNReal) := by
    simpa only [tsum_fintype] using q.tsum_coe
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, hq,
    mul_one, mul_one]
  norm_cast
  exact tsub_add_cancel_of_le ht

@[simp]
theorem mixDistribution_apply
    {α : Type u} [Fintype α]
    (t : NNReal) (ht : t ≤ 1) (p q : Distribution α) (a : α) :
    mixDistribution t ht p q a =
      ((1 - t : NNReal) : ENNReal) * p a + (t : ENNReal) * q a :=
  rfl

theorem mixDistribution_apply_toReal
    {α : Type u} [Fintype α]
    (t : NNReal) (ht : t ≤ 1) (p q : Distribution α) (a : α) :
    (mixDistribution t ht p q a).toReal =
      (1 - (t : ℝ)) * (p a).toReal + (t : ℝ) * (q a).toReal := by
  rw [mixDistribution_apply, ENNReal.toReal_add
    (ENNReal.mul_ne_top (by simp) (p.apply_ne_top a))
    (ENNReal.mul_ne_top (by simp) (q.apply_ne_top a))]
  simp only [ENNReal.toReal_mul]
  change ((1 - t : NNReal) : ℝ) * (p a).toReal + (t : ℝ) * (q a).toReal = _
  rw [NNReal.coe_sub ht]
  norm_num

/-- A family of distributions closed under finite convex mixtures. -/
def IsConvexDistributionFamily
    {α : Type u} [Fintype α]
    (feasible : Distribution α → Prop) : Prop :=
  ∀ ⦃p q⦄, feasible p → feasible q →
    ∀ (t : NNReal) (ht : t ≤ 1), feasible (mixDistribution t ht p q)

private theorem entropyTerm_nonneg
    {α : Type u} (p : Distribution α) (a : α) :
    0 ≤ Real.negMulLog (p a).toReal := by
  apply Real.negMulLog_nonneg ENNReal.toReal_nonneg
  have hpa : p a ≤ 1 := p.coe_le_one a
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hpa

private theorem entropyTerm_mix_ge_left
    {α : Type u} [Fintype α]
    (t : NNReal) (ht : t ≤ 1) (p q : Distribution α) (a : α) :
    (1 - (t : ℝ)) * Real.negMulLog (p a).toReal ≤
      Real.negMulLog (mixDistribution t ht p q a).toReal := by
  have htRealNonneg : 0 ≤ (t : ℝ) := t.2
  have htRealLe : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have hOneSub : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr htRealLe
  have hCoeff : (1 - (t : ℝ)) + (t : ℝ) = 1 := by ring
  have hConcave := Real.concaveOn_negMulLog.2
    (show (p a).toReal ∈ Set.Ici (0 : ℝ) from ENNReal.toReal_nonneg)
    (show (q a).toReal ∈ Set.Ici (0 : ℝ) from ENNReal.toReal_nonneg)
    hOneSub htRealNonneg hCoeff
  rw [mixDistribution_apply_toReal]
  have hRightNonneg :
      0 ≤ (t : ℝ) * Real.negMulLog (q a).toReal :=
    mul_nonneg htRealNonneg (entropyTerm_nonneg q a)
  dsimp only [smul_eq_mul] at hConcave
  linarith

/-- Keeping the exceptional coordinate exact and using concavity on every
other coordinate gives the quantitative lower bound needed at the boundary
of the simplex. -/
theorem shannonEntropy_mix_lower_bound_of_apply_eq_zero
    {α : Type u} [Fintype α] [DecidableEq α]
    (t : NNReal) (ht : t ≤ 1) (p q : Distribution α) (a : α)
    (hpa : p a = 0) :
    (1 - (t : ℝ)) * shannonEntropy p +
        Real.negMulLog ((t : ℝ) * (q a).toReal) ≤
      shannonEntropy (mixDistribution t ht p q) := by
  classical
  let rest : Finset α := Finset.univ.erase a
  have haUniv : a ∈ (Finset.univ : Finset α) := Finset.mem_univ a
  have hPointwise : ∀ x ∈ rest,
      (1 - (t : ℝ)) * Real.negMulLog (p x).toReal ≤
        Real.negMulLog (mixDistribution t ht p q x).toReal := by
    intro x _
    exact entropyTerm_mix_ge_left t ht p q x
  have hSum := Finset.sum_le_sum hPointwise
  have hpSplit :
      shannonEntropy p =
        (∑ x ∈ rest, Real.negMulLog (p x).toReal) := by
    unfold shannonEntropy
    rw [← Finset.sum_erase_add _ _ haUniv]
    simp [rest, hpa]
  have hMixSplit :
      shannonEntropy (mixDistribution t ht p q) =
        (∑ x ∈ rest, Real.negMulLog (mixDistribution t ht p q x).toReal) +
          Real.negMulLog ((t : ℝ) * (q a).toReal) := by
    unfold shannonEntropy
    rw [← Finset.sum_erase_add _ _ haUniv]
    rw [mixDistribution_apply_toReal, hpa]
    simp [rest]
  rw [hpSplit, hMixSplit]
  have hSum' :
      (1 - (t : ℝ)) * (∑ x ∈ rest, Real.negMulLog (p x).toReal) ≤
        ∑ x ∈ rest, Real.negMulLog (mixDistribution t ht p q x).toReal := by
    simpa only [Finset.mul_sum] using hSum
  linarith

/-- A concrete boundary scale at which the newly activated coordinate's
`-t log t` contribution dominates the linear entropy loss on the old
support. -/
noncomputable def supportGainScale
    {α : Type u} [Fintype α]
    (p q : Distribution α) (a : α) : NNReal :=
  Real.toNNReal (Real.exp (-((shannonEntropy p + 1) / (q a).toReal)))

theorem supportGainScale_pos
    {α : Type u} [Fintype α]
    (p q : Distribution α) (a : α) :
    0 < supportGainScale p q a := by
  rw [supportGainScale, Real.toNNReal_pos]
  exact Real.exp_pos _

theorem supportGainScale_lt_one_of_mem_support
    {α : Type u} [Fintype α]
    (p q : Distribution α) {a : α} (ha : a ∈ q.support) :
    supportGainScale p q a < 1 := by
  rw [supportGainScale, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ (Real.exp_pos _).le]
  norm_num only [NNReal.coe_one]
  rw [Real.exp_lt_one_iff]
  have hqPos : 0 < (q a).toReal := by
    exact ENNReal.toReal_pos ((PMF.mem_support_iff q a).1 ha) (q.apply_ne_top a)
  have hEntropyNonneg : 0 ≤ shannonEntropy p := shannonEntropy_nonneg p
  exact neg_neg_of_pos (div_pos (by linarith) hqPos)

theorem shannonEntropy_lt_mix_supportGainScale
    {α : Type u} [Fintype α] [DecidableEq α]
    (p q : Distribution α) {a : α}
    (hpa : p a = 0) (ha : a ∈ q.support) :
    shannonEntropy p <
      shannonEntropy
        (mixDistribution (supportGainScale p q a)
          (supportGainScale_lt_one_of_mem_support p q ha).le p q) := by
  let t : NNReal := supportGainScale p q a
  have htLe : t ≤ 1 := (supportGainScale_lt_one_of_mem_support p q ha).le
  have htPos : 0 < (t : ℝ) := by
    exact_mod_cast supportGainScale_pos p q a
  have hqPos : 0 < (q a).toReal := by
    exact ENNReal.toReal_pos ((PMF.mem_support_iff q a).1 ha) (q.apply_ne_top a)
  have hLogT : Real.log (t : ℝ) =
      -((shannonEntropy p + 1) / (q a).toReal) := by
    rw [show (t : ℝ) = Real.exp
      (-((shannonEntropy p + 1) / (q a).toReal)) by
        simp [t, supportGainScale, Real.coe_toNNReal _ (Real.exp_pos _).le]]
    exact Real.log_exp _
  have hLogQ : Real.log ((t : ℝ) * (q a).toReal) =
      Real.log (t : ℝ) + Real.log (q a).toReal :=
    Real.log_mul htPos.ne' hqPos.ne'
  have hGain :
      shannonEntropy p <
        (1 - (t : ℝ)) * shannonEntropy p +
          Real.negMulLog ((t : ℝ) * (q a).toReal) := by
    rw [show Real.negMulLog ((t : ℝ) * (q a).toReal) =
      -((t : ℝ) * (q a).toReal) *
        Real.log ((t : ℝ) * (q a).toReal) by rfl]
    rw [hLogQ, hLogT]
    have hqLe : (q a).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (q.coe_le_one a)
    have hLogNonpos : Real.log (q a).toReal ≤ 0 :=
      Real.log_nonpos hqPos.le hqLe
    have hCancel :
        (q a).toReal * ((shannonEntropy p + 1) / (q a).toReal) =
          shannonEntropy p + 1 := by
      field_simp
    have hAlgebra :
        (1 - (t : ℝ)) * shannonEntropy p +
            -((t : ℝ) * (q a).toReal) *
              (-((shannonEntropy p + 1) / (q a).toReal) +
                Real.log (q a).toReal) =
          shannonEntropy p + (t : ℝ) -
            (t : ℝ) * (q a).toReal * Real.log (q a).toReal := by
      calc
        _ = shannonEntropy p - (t : ℝ) * shannonEntropy p +
              (t : ℝ) *
                ((q a).toReal * ((shannonEntropy p + 1) / (q a).toReal)) -
              (t : ℝ) * (q a).toReal * Real.log (q a).toReal := by ring
        _ = _ := by rw [hCancel]; ring
    rw [hAlgebra]
    have hProductNonpos :
        (t : ℝ) * (q a).toReal * Real.log (q a).toReal ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg htPos.le hqPos.le) hLogNonpos
    linarith
  exact lt_of_lt_of_le hGain
    (shannonEntropy_mix_lower_bound_of_apply_eq_zero t htLe p q a hpa)

/-- **Lemma `lem:max-support`.** An entropy maximizer over a convex family of
finite distributions has support equal to the union of all feasible
supports. -/
theorem support_eq_iUnion_of_isMaxEntropyAmong
    {α : Type u} [Fintype α] [DecidableEq α]
    {feasible : Distribution α → Prop} {p : Distribution α}
    (hConvex : IsConvexDistributionFamily feasible)
    (hMax : IsMaxEntropyAmong feasible p) :
    p.support = ⋃ q : Distribution α, ⋃ (_ : feasible q), q.support := by
  ext a
  constructor
  · intro ha
    simp only [Set.mem_iUnion]
    exact ⟨p, hMax.1, ha⟩
  · simp only [Set.mem_iUnion]
    rintro ⟨q, hqFeasible, ha⟩
    by_contra hpaSupport
    have hpa : p a = 0 := (p.apply_eq_zero_iff a).2 hpaSupport
    let t : NNReal := supportGainScale p q a
    have htLe : t ≤ 1 := (supportGainScale_lt_one_of_mem_support p q ha).le
    have hMixFeasible : feasible (mixDistribution t htLe p q) :=
      hConvex hMax.1 hqFeasible t htLe
    have hUpper := hMax.2 (mixDistribution t htLe p q) hMixFeasible
    have hLower := shannonEntropy_lt_mix_supportGainScale p q hpa ha
    exact (not_lt_of_ge hUpper) hLower

theorem monomialMoment_mixDistribution
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (t : NNReal) (ht : t ≤ 1)
    (p q : Distribution (Assignment Var)) (scope : Finset Var) :
    monomialMoment (mixDistribution t ht p q) scope =
      (1 - (t : ℝ)) * monomialMoment p scope +
        (t : ℝ) * monomialMoment q scope := by
  classical
  unfold monomialMoment
  simp_rw [mixDistribution_apply_toReal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sameFeatureMomentsUpTo_isConvex
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    IsConvexDistributionFamily (SameFeatureMomentsUpTo k p) := by
  intro q r hq hr t ht scope hScope
  rw [monomialMoment_mixDistribution, hq scope hScope, hr scope hScope]
  ring

/-- The maximal-support lemma specialized to the canonical feature-moment
fiber of a `k`-local law. -/
theorem support_eq_iUnion_sameFeatureMoments_of_isKLocal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var))
    (hLocal : IsKLocalMarginal k p) :
    p.support = ⋃ q : Distribution (Assignment Var),
      ⋃ (_ : SameFeatureMomentsUpTo k p q), q.support := by
  apply support_eq_iUnion_of_isMaxEntropyAmong
    (sameFeatureMomentsUpTo_isConvex k p)
  exact (isKLocalMarginal_iff_maxEntropy_sameFeatureMoments k p).1 hLocal

theorem support_subset_of_sameFeatureMoments_of_isKLocal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) {p q : Distribution (Assignment Var)}
    (hLocal : IsKLocalMarginal k p)
    (hMoments : SameFeatureMomentsUpTo k p q) :
    q.support ⊆ p.support := by
  rw [support_eq_iUnion_sameFeatureMoments_of_isKLocal k p hLocal]
  exact Set.subset_iUnion_of_subset q
    (Set.subset_iUnion_of_subset hMoments Set.Subset.rfl)

end KLocality
