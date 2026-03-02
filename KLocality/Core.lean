import Mathlib

namespace KLocality

open scoped BigOperators

universe u v

/-- Discrete distributions are PMFs. -/
abbrev Distribution (α : Type u) := PMF α

/-- `n`-bit strings, used for observed variables in circuit statements. -/
abbrev BitVec (n : Nat) : Type := Fin n → Bool

/-- Boolean assignments over a variable index type. -/
abbrev Assignment (Var : Type u) : Type u := Var → Bool

/-- Restrict a global assignment to a finite scope. -/
def restrict {Var : Type u} (scope : Finset Var) (x : Assignment Var) : Assignment scope :=
  fun i => x i.1

/-- Marginal of a PMF on a finite scope. -/
noncomputable def marginal
    {Var : Type u} [DecidableEq Var]
    (scope : Finset Var) (p : Distribution (Assignment Var)) :
    Distribution (Assignment scope) :=
  p.map (restrict scope)

/-- A scoped marginal constraint: the target PMF on a finite variable scope. -/
structure MarginalConstraint (Var : Type u) [DecidableEq Var] where
  scope : Finset Var
  target : Distribution (Assignment scope)

/-- Distribution `p` satisfies one scoped marginal constraint. -/
def SatisfiesMarginal
    {Var : Type u} [DecidableEq Var]
    (p : Distribution (Assignment Var)) (c : MarginalConstraint Var) : Prop :=
  marginal c.scope p = c.target

/-- Distribution `p` satisfies all listed scoped marginal constraints. -/
def FeasibleMarginals
    {Var : Type u} [DecidableEq Var]
    (constraints : List (MarginalConstraint Var))
    (p : Distribution (Assignment Var)) : Prop :=
  ∀ c ∈ constraints, SatisfiesMarginal p c

/-- Every listed scope has cardinality at most `k`. -/
def MarginalConstraintsRespectK
    {Var : Type u} [DecidableEq Var]
    (k : Nat) (constraints : List (MarginalConstraint Var)) : Prop :=
  ∀ c ∈ constraints, c.scope.card ≤ k

theorem marginalConstraintsRespectK_mono
    {Var : Type u} [DecidableEq Var]
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {constraints : List (MarginalConstraint Var)} :
    MarginalConstraintsRespectK kSmall constraints →
      MarginalConstraintsRespectK kLarge constraints := by
  intro h c hc
  exact Nat.le_trans (h c hc) hkl

/-- Uniform PMF on a nonempty finite set. -/
noncomputable abbrev uniformOn
    {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) : Distribution α :=
  PMF.uniformOfFinset s hs

theorem uniformOn_apply_of_mem
    {α : Type u} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∈ s) :
    uniformOn s hs a = (s.card : ENNReal)⁻¹ := by
  simpa [uniformOn] using PMF.uniformOfFinset_apply_of_mem (s := s) (hs := hs) ha

theorem uniformOn_apply_of_notMem
    {α : Type u} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∉ s) :
    uniformOn s hs a = 0 := by
  simpa [uniformOn] using PMF.uniformOfFinset_apply_of_notMem (s := s) (hs := hs) ha

@[simp]
theorem support_uniformOn
    {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) :
    (uniformOn s hs).support = (s : Set α) := by
  simp [uniformOn]

/-- Shannon entropy in nats. -/
noncomputable def shannonEntropy
    {α : Type u} [Fintype α] (p : Distribution α) : ℝ :=
  ∑ a, Real.negMulLog (ENNReal.toReal (p a))

theorem shannonEntropy_nonneg
    {α : Type u} [Fintype α] (p : Distribution α) :
    0 ≤ shannonEntropy p := by
  unfold shannonEntropy
  refine Finset.sum_nonneg ?_
  intro a _
  refine Real.negMulLog_nonneg ENNReal.toReal_nonneg ?_
  have hpa : p a ≤ 1 := p.coe_le_one a
  have htoReal : ENNReal.toReal (p a) ≤ ENNReal.toReal (1 : ENNReal) :=
    ENNReal.toReal_mono ENNReal.one_ne_top hpa
  simpa using htoReal

lemma negMulLog_le_one_sub (x : ℝ) (hx : 0 ≤ x) : Real.negMulLog x ≤ 1 - x := by
  have hkl : 0 ≤ InformationTheory.klFun x := InformationTheory.klFun_nonneg hx
  have hkl' : 0 ≤ -Real.negMulLog x + 1 - x := by
    simpa [InformationTheory.klFun, Real.negMulLog_def, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hkl
  linarith

lemma sum_toReal_eq_one_of_support_subset
    {α : Type*}
    (p : Distribution α) (s : Finset α)
    (hsub : p.support ⊆ (s : Set α)) :
    Finset.sum s (fun a => ENNReal.toReal (p a)) = 1 := by
  have hsum_s_enn : Finset.sum s (fun a => p a) = (1 : ENNReal) := by
    calc
      Finset.sum s (fun a => p a) = ∑' a, p a := by
        symm
        refine tsum_eq_sum ?_
        intro a ha_not_s
        exact (p.apply_eq_zero_iff a).2 (by
          intro ha_support
          exact ha_not_s (hsub ha_support))
      _ = 1 := p.tsum_coe
  have hsum_s_real : (Finset.sum s (fun a => p a)).toReal =
      Finset.sum s (fun a => ENNReal.toReal (p a)) := by
    simpa using (ENNReal.toReal_sum (s := s) (f := fun a => p a) (fun a _ => p.apply_ne_top a))
  have hreal : (1 : ENNReal).toReal = Finset.sum s (fun a => ENNReal.toReal (p a)) := by
    simpa [hsum_s_enn] using hsum_s_real
  simpa using hreal.symm

lemma shannonEntropy_eq_sum_on_finset_of_support_subset
    {α : Type*} [Fintype α]
    (p : Distribution α) (s : Finset α)
    (hsub : p.support ⊆ (s : Set α)) :
    shannonEntropy p = Finset.sum s (fun a => Real.negMulLog (ENNReal.toReal (p a))) := by
  unfold shannonEntropy
  have hsum_eq :
      Finset.sum s (fun a => Real.negMulLog (ENNReal.toReal (p a))) =
      Finset.sum (Finset.univ : Finset α) (fun a => Real.negMulLog (ENNReal.toReal (p a))) := by
    refine Finset.sum_subset (by intro a _; simp) ?_
    intro a _ ha_not_s
    have hnot_support : a ∉ p.support := by
      intro ha_support
      exact ha_not_s (hsub ha_support)
    have hpzero : p a = 0 := (p.apply_eq_zero_iff a).2 hnot_support
    simp [hpzero]
  exact hsum_eq.symm

theorem shannonEntropy_le_log_card_of_support_subset
    {α : Type*} [Fintype α]
    (p : Distribution α) (s : Finset α) (hs : s.Nonempty)
    (hsub : p.support ⊆ (s : Set α)) :
    shannonEntropy p ≤ Real.log (s.card : ℝ) := by
  let m : ℝ := (s.card : ℝ)
  have hm_nat_pos : 0 < s.card := Finset.card_pos.mpr hs
  have hm_pos_card : 0 < (s.card : ℝ) := by
    exact_mod_cast hm_nat_pos
  have hm_pos : 0 < m := by simpa [m] using hm_pos_card
  have hm_nonneg : 0 ≤ m := le_of_lt hm_pos
  let pa : α → ℝ := fun a => ENNReal.toReal (p a)
  have hpa_nonneg : ∀ a, 0 ≤ pa a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hsum_pa : Finset.sum s pa = 1 := by
    simpa [pa] using sum_toReal_eq_one_of_support_subset p s hsub
  have hpoint : ∀ a ∈ s, Real.negMulLog (m * pa a) ≤ 1 - m * pa a := by
    intro a ha
    exact negMulLog_le_one_sub (m * pa a) (mul_nonneg hm_nonneg (hpa_nonneg a))
  have hsum_ineq : Finset.sum s (fun a => Real.negMulLog (m * pa a))
      ≤ Finset.sum s (fun a => (1 - m * pa a)) := by
    exact Finset.sum_le_sum hpoint
  have hsum_right : Finset.sum s (fun a => (1 - m * pa a)) = 0 := by
    calc
      Finset.sum s (fun a => (1 - m * pa a))
          = Finset.sum s (fun _ => (1 : ℝ)) - Finset.sum s (fun a => m * pa a) := by
              simp [Finset.sum_sub_distrib]
      _ = (s.card : ℝ) - m * Finset.sum s pa := by
            rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
            simp
      _ = (s.card : ℝ) - m := by rw [hsum_pa, mul_one]
      _ = 0 := by simp [m]
  have hsum_left : Finset.sum s (fun a => Real.negMulLog (m * pa a))
      = m * Finset.sum s (fun a => Real.negMulLog (pa a))
        + Real.negMulLog m * Finset.sum s pa := by
    calc
      Finset.sum s (fun a => Real.negMulLog (m * pa a))
          = Finset.sum s (fun a => (pa a * Real.negMulLog m + m * Real.negMulLog (pa a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.negMulLog_mul m (pa a))
      _ = Finset.sum s (fun a => pa a * Real.negMulLog m)
          + Finset.sum s (fun a => m * Real.negMulLog (pa a)) := by
              exact Finset.sum_add_distrib
      _ = (Finset.sum s pa) * Real.negMulLog m
          + m * Finset.sum s (fun a => Real.negMulLog (pa a)) := by
              rw [Finset.sum_mul, Finset.mul_sum]
      _ = m * Finset.sum s (fun a => Real.negMulLog (pa a))
          + Real.negMulLog m * Finset.sum s pa := by ring
  have hmain : m * Finset.sum s (fun a => Real.negMulLog (pa a))
      + Real.negMulLog m * Finset.sum s pa ≤ 0 := by
    calc
      m * Finset.sum s (fun a => Real.negMulLog (pa a)) + Real.negMulLog m * Finset.sum s pa
          = Finset.sum s (fun a => Real.negMulLog (m * pa a)) := by
              simp [hsum_left]
      _ ≤ Finset.sum s (fun a => (1 - m * pa a)) := hsum_ineq
      _ = 0 := hsum_right
  have hmain' : m * Finset.sum s (fun a => Real.negMulLog (pa a)) + Real.negMulLog m ≤ 0 := by
    simpa [hsum_pa] using hmain
  have hmain'' : m * (Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m) ≤ 0 := by
    have : m * Finset.sum s (fun a => Real.negMulLog (pa a)) - m * Real.log m ≤ 0 := by
      simpa [Real.negMulLog_def, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hmain'
    simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using this
  have hbound_sum : Finset.sum s (fun a => Real.negMulLog (pa a)) ≤ Real.log m := by
    have hsub' : Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m ≤ 0 := by
      by_contra hnot
      have hgt : 0 < Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m :=
        lt_of_not_ge hnot
      have hmul_pos : 0 < m * (Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m) :=
        mul_pos hm_pos hgt
      exact not_lt_of_ge hmain'' hmul_pos
    exact sub_nonpos.mp hsub'
  have hentropy_s : shannonEntropy p = Finset.sum s (fun a => Real.negMulLog (pa a)) := by
    simpa [pa] using shannonEntropy_eq_sum_on_finset_of_support_subset p s hsub
  calc
    shannonEntropy p = Finset.sum s (fun a => Real.negMulLog (pa a)) := hentropy_s
    _ ≤ Real.log m := hbound_sum
    _ = Real.log (s.card : ℝ) := by simp [m]

theorem shannonEntropy_uniformOn
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) :
    shannonEntropy (uniformOn s hs) = Real.log (s.card : ℝ) := by
  have hsub : (uniformOn s hs).support ⊆ (s : Set α) := by
    simp [support_uniformOn s hs]
  calc
    shannonEntropy (uniformOn s hs)
        = Finset.sum s
            (fun a => Real.negMulLog (ENNReal.toReal ((uniformOn s hs) a))) :=
          shannonEntropy_eq_sum_on_finset_of_support_subset (uniformOn s hs) s hsub
    _ = Finset.sum s (fun _ => Real.negMulLog (ENNReal.toReal ((s.card : ENNReal)⁻¹))) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [uniformOn_apply_of_mem hs ha]
    _ = (s.card : ℝ) * Real.negMulLog (ENNReal.toReal ((s.card : ENNReal)⁻¹)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ) * ((s.card : ℝ)⁻¹ * Real.log (s.card : ℝ)) := by
          congr 1
          calc
            Real.negMulLog (ENNReal.toReal ((s.card : ENNReal)⁻¹))
                = Real.negMulLog ((s.card : ℝ)⁻¹) := by
                    simp [ENNReal.toReal_inv, ENNReal.toReal_natCast]
            _ = -((s.card : ℝ)⁻¹ * Real.log ((s.card : ℝ)⁻¹)) := by
                    simp [Real.negMulLog_def]
            _ = -((s.card : ℝ)⁻¹ * (-Real.log (s.card : ℝ))) := by
                    rw [Real.log_inv]
            _ = (s.card : ℝ)⁻¹ * Real.log (s.card : ℝ) := by ring
    _ = Real.log (s.card : ℝ) := by
          have hcard_ne_zero : (s.card : ℝ) ≠ 0 := by
            exact_mod_cast hs.card_ne_zero
          calc
            (s.card : ℝ) * ((s.card : ℝ)⁻¹ * Real.log (s.card : ℝ))
                = ((s.card : ℝ) * (s.card : ℝ)⁻¹) * Real.log (s.card : ℝ) := by ring
            _ = Real.log (s.card : ℝ) := by simp [hcard_ne_zero]

/-- `p` is a maximum-entropy point among PMFs satisfying predicate `feasible`. -/
def IsMaxEntropyAmong
    {α : Type u} [Fintype α]
    (feasible : Distribution α → Prop) (p : Distribution α) : Prop :=
  feasible p ∧ ∀ q, feasible q → shannonEntropy q ≤ shannonEntropy p

/-- Local completeness for marginal constraints:
every assignment outside `target` violates at least one constrained local pattern. -/
def MarginalLocalCompleteness
    {Var : Type u} [DecidableEq Var]
    (target : Set (Assignment Var))
    (constraints : List (MarginalConstraint Var)) : Prop :=
  ∀ x, x ∉ target → ∃ c ∈ constraints, c.target (restrict c.scope x) = 0

lemma marginal_at_projection_nonzero_of_mem_support
    {Var : Type u} [DecidableEq Var]
    (q : Distribution (Assignment Var)) (scope : Finset Var)
    {x : Assignment Var} (hx : x ∈ q.support) :
    marginal scope q (restrict scope x) ≠ 0 := by
  have hxImage : restrict scope x ∈ (marginal scope q).support := by
    rw [marginal, PMF.support_map]
    exact ⟨x, hx, rfl⟩
  exact (PMF.mem_support_iff (marginal scope q) (restrict scope x)).1 hxImage

theorem support_subset_of_marginalLocalCompleteness
    {Var : Type u} [DecidableEq Var]
    {constraints : List (MarginalConstraint Var)}
    {target : Set (Assignment Var)}
    {q : Distribution (Assignment Var)}
    (hFeasible : FeasibleMarginals constraints q)
    (hComplete : MarginalLocalCompleteness target constraints) :
    q.support ⊆ target := by
  intro x hx
  by_contra hxNot
  rcases hComplete x hxNot with ⟨c, hcIn, hcZero⟩
  have hMargNonzero : marginal c.scope q (restrict c.scope x) ≠ 0 :=
    marginal_at_projection_nonzero_of_mem_support q c.scope hx
  have hEq : marginal c.scope q = c.target := hFeasible c hcIn
  have hTargetNonzero : c.target (restrict c.scope x) ≠ 0 := by
    simpa [hEq] using hMargNonzero
  exact hTargetNonzero hcZero

/-- Local verification in the marginal setting:
if feasible PMFs are forced into finite `target`, then `uniformOn target` is max-entropy feasible. -/
theorem localVerificationMaximumEntropyMarginalsOnFinset
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (target : Finset (Assignment Var)) (hTarget : target.Nonempty)
    (constraints : List (MarginalConstraint Var))
    (hComplete : MarginalLocalCompleteness (target : Set (Assignment Var)) constraints)
    (hUniformFeasible : FeasibleMarginals constraints (uniformOn target hTarget)) :
    IsMaxEntropyAmong (FeasibleMarginals constraints) (uniformOn target hTarget) := by
  refine ⟨hUniformFeasible, ?_⟩
  intro q hq
  have hqSupportTarget : q.support ⊆ (target : Set (Assignment Var)) :=
    support_subset_of_marginalLocalCompleteness hq hComplete
  have hbound := shannonEntropy_le_log_card_of_support_subset q target hTarget hqSupportTarget
  have huniform : shannonEntropy (uniformOn target hTarget) = Real.log (target.card : ℝ) :=
    shannonEntropy_uniformOn target hTarget
  simpa [huniform] using hbound

/-- A distribution on assignments is `k`-local if it is max-entropy under
scoped marginal constraints of arity at most `k`. -/
def IsKLocalMarginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) : Prop :=
  ∃ constraints : List (MarginalConstraint Var),
    MarginalConstraintsRespectK k constraints ∧
      IsMaxEntropyAmong (FeasibleMarginals constraints) p

/-- Local-verification `k`-locality certificate in the marginal setting. -/
theorem localVerificationIsKLocalMarginalOnFinset
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat)
    (target : Finset (Assignment Var)) (hTarget : target.Nonempty)
    (constraints : List (MarginalConstraint Var))
    (hBound : MarginalConstraintsRespectK k constraints)
    (hComplete : MarginalLocalCompleteness (target : Set (Assignment Var)) constraints)
    (hUniformFeasible : FeasibleMarginals constraints (uniformOn target hTarget)) :
    IsKLocalMarginal k (uniformOn target hTarget) := by
  refine ⟨constraints, hBound, ?_⟩
  exact localVerificationMaximumEntropyMarginalsOnFinset target hTarget constraints hComplete
    hUniformFeasible

theorem isKLocalMarginal_mono
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {p : Distribution (Assignment Var)} :
    IsKLocalMarginal kSmall p → IsKLocalMarginal kLarge p := by
  intro h
  rcases h with ⟨constraints, hBound, hMax⟩
  exact ⟨constraints, marginalConstraintsRespectK_mono hkl hBound, hMax⟩

/-- Projection of a joint assignment `(ObsVar ⊕ LatVar) → Bool` to observed coordinates. -/
def projectObs
    {ObsVar : Type u} {LatVar : Type v}
    (z : Assignment (Sum ObsVar LatVar)) : Assignment ObsVar :=
  fun i => z (Sum.inl i)

/-- `pJoint` is a marginal model of `pObs` when observed projection recovers `pObs`. -/
def IsMarginalModel
    {ObsVar : Type u} {LatVar : Type v}
    (pObs : Distribution (Assignment ObsVar))
    (pJoint : Distribution (Assignment (Sum ObsVar LatVar))) : Prop :=
  pJoint.map projectObs = pObs

/-- A `k`-localization of an observed distribution with latent variable type `LatVar`. -/
structure KLocalization
    (k : Nat)
    (ObsVar : Type u) (LatVar : Type v)
    [DecidableEq ObsVar] [Fintype ObsVar]
    [DecidableEq LatVar] [Fintype LatVar]
    (pObs : Distribution (Assignment ObsVar)) where
  lifted : Distribution (Assignment (Sum ObsVar LatVar))
  marginal : IsMarginalModel pObs lifted
  kLocal : IsKLocalMarginal k lifted

/-- Concrete local-verification witness that constructs a `k`-localization. -/
structure LocalVerificationWitness
    (k : Nat)
    (ObsVar : Type u) (LatVar : Type v)
    [DecidableEq ObsVar] [Fintype ObsVar]
    [DecidableEq LatVar] [Fintype LatVar]
    (pObs : Distribution (Assignment ObsVar)) where
  target : Finset (Assignment (Sum ObsVar LatVar))
  targetNonempty : target.Nonempty
  constraints : List (MarginalConstraint (Sum ObsVar LatVar))
  bound : MarginalConstraintsRespectK k constraints
  complete : MarginalLocalCompleteness (target : Set (Assignment (Sum ObsVar LatVar))) constraints
  uniformFeasible : FeasibleMarginals constraints (uniformOn target targetNonempty)
  marginal : IsMarginalModel pObs (uniformOn target targetNonempty)

/-- Build a `k`-localization directly from a local-verification witness. -/
noncomputable def kLocalizationOfWitness
    {k : Nat}
    {ObsVar : Type u} {LatVar : Type v}
    [DecidableEq ObsVar] [Fintype ObsVar]
    [DecidableEq LatVar] [Fintype LatVar]
    {pObs : Distribution (Assignment ObsVar)}
    (w : LocalVerificationWitness k ObsVar LatVar pObs) :
    KLocalization k ObsVar LatVar pObs :=
  { lifted := uniformOn w.target w.targetNonempty
    marginal := w.marginal
    kLocal :=
      localVerificationIsKLocalMarginalOnFinset k w.target w.targetNonempty w.constraints
        w.bound w.complete w.uniformFeasible }

/-- Existence of a `k`-localization using exactly `latentVars` Boolean latent variables. -/
def HasKLocalization
    (k latentVars : Nat) (ObsVar : Type u)
    [DecidableEq ObsVar] [Fintype ObsVar]
    (pObs : Distribution (Assignment ObsVar)) : Prop :=
  Nonempty (KLocalization k ObsVar (Fin latentVars) pObs)

theorem hasKLocalization_mono
    {ObsVar : Type u} [DecidableEq ObsVar] [Fintype ObsVar]
    {pObs : Distribution (Assignment ObsVar)} {latentVars : Nat}
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge) :
    HasKLocalization kSmall latentVars ObsVar pObs →
      HasKLocalization kLarge latentVars ObsVar pObs := by
  intro h
  rcases h with ⟨w⟩
  refine ⟨{ lifted := w.lifted, marginal := w.marginal, kLocal := ?_ }⟩
  exact isKLocalMarginal_mono hkl w.kLocal

/-- Bit-vector specialization used by circuit-complexity statements. -/
abbrev HasKLocalizationBits
    (k latentBits n : Nat) (pObs : Distribution (BitVec n)) : Prop :=
  HasKLocalization k latentBits (Fin n) pObs

theorem hasKLocalizationBits_mono
    {n : Nat} {pObs : Distribution (BitVec n)} {latentBits : Nat}
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge) :
    HasKLocalizationBits kSmall latentBits n pObs →
      HasKLocalizationBits kLarge latentBits n pObs :=
  hasKLocalization_mono (ObsVar := Fin n) (pObs := pObs) (latentVars := latentBits) hkl

/-- Witness-to-existence conversion in latent-bit form. -/
theorem hasKLocalizationBits_of_localVerificationWitness
    {k n latentBits : Nat}
    {pObs : Distribution (BitVec n)}
    (w : LocalVerificationWitness k (Fin n) (Fin latentBits) pObs) :
    HasKLocalizationBits k latentBits n pObs := by
  exact ⟨kLocalizationOfWitness w⟩

/-- `LC_k(D)`: minimal latent-variable count among `k`-localizations, assuming existence. -/
noncomputable def localizationComplexity
    (k : Nat) (ObsVar : Type u)
    [DecidableEq ObsVar] [Fintype ObsVar]
    (pObs : Distribution (Assignment ObsVar))
    (hExists : ∃ m, HasKLocalization k m ObsVar pObs) : Nat := by
  classical
  exact Nat.find hExists

theorem localizationComplexity_spec
    (k : Nat) (ObsVar : Type u)
    [DecidableEq ObsVar] [Fintype ObsVar]
    (pObs : Distribution (Assignment ObsVar))
    (hExists : ∃ m, HasKLocalization k m ObsVar pObs) :
    HasKLocalization k (localizationComplexity k ObsVar pObs hExists) ObsVar pObs := by
  classical
  exact Nat.find_spec hExists

theorem localizationComplexity_min
    (k : Nat) (ObsVar : Type u)
    [DecidableEq ObsVar] [Fintype ObsVar]
    (pObs : Distribution (Assignment ObsVar))
    (hExists : ∃ m, HasKLocalization k m ObsVar pObs) :
    ∀ m, HasKLocalization k m ObsVar pObs →
      localizationComplexity k ObsVar pObs hExists ≤ m := by
  classical
  intro m hm
  exact Nat.find_min' hExists hm

theorem localizationComplexity_mono
    {ObsVar : Type u} [DecidableEq ObsVar] [Fintype ObsVar]
    {pObs : Distribution (Assignment ObsVar)}
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    (hSmall : ∃ m, HasKLocalization kSmall m ObsVar pObs)
    (hLarge : ∃ m, HasKLocalization kLarge m ObsVar pObs) :
    localizationComplexity kLarge ObsVar pObs hLarge ≤
      localizationComplexity kSmall ObsVar pObs hSmall := by
  apply localizationComplexity_min kLarge ObsVar pObs hLarge
  exact hasKLocalization_mono hkl (localizationComplexity_spec kSmall ObsVar pObs hSmall)

/-- `LC_k(D)` in bit-vector form for observed `n`-bit distributions. -/
noncomputable abbrev localizationComplexityBits
    (k n : Nat)
    (pObs : Distribution (BitVec n))
    (hExists : ∃ ℓ, HasKLocalizationBits k ℓ n pObs) : Nat :=
  localizationComplexity k (Fin n) pObs hExists

theorem localizationComplexityBits_spec
    (k n : Nat)
    (pObs : Distribution (BitVec n))
    (hExists : ∃ ℓ, HasKLocalizationBits k ℓ n pObs) :
    HasKLocalizationBits k (localizationComplexityBits k n pObs hExists) n pObs :=
  localizationComplexity_spec k (Fin n) pObs hExists

theorem localizationComplexityBits_min
    (k n : Nat)
    (pObs : Distribution (BitVec n))
    (hExists : ∃ ℓ, HasKLocalizationBits k ℓ n pObs) :
    ∀ ℓ, HasKLocalizationBits k ℓ n pObs →
      localizationComplexityBits k n pObs hExists ≤ ℓ :=
  localizationComplexity_min k (Fin n) pObs hExists

theorem localizationComplexityBits_mono
    {n : Nat} {pObs : Distribution (BitVec n)}
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    (hSmall : ∃ ℓ, HasKLocalizationBits kSmall ℓ n pObs)
    (hLarge : ∃ ℓ, HasKLocalizationBits kLarge ℓ n pObs) :
    localizationComplexityBits kLarge n pObs hLarge ≤
      localizationComplexityBits kSmall n pObs hSmall :=
  localizationComplexity_mono (ObsVar := Fin n) (pObs := pObs) hkl hSmall hLarge

/-- Paper-style notation alias for `LC_k(D)` on `n` observed bits. -/
noncomputable abbrev LC_k
    (k n : Nat)
    (D : Distribution (BitVec n))
    (hExists : ∃ ℓ, HasKLocalizationBits k ℓ n D) : Nat :=
  localizationComplexityBits k n D hExists

end KLocality
