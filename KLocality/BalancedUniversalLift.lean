import KLocality.BlockFeatureLift
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field

namespace KLocality

open scoped BigOperators
noncomputable section

namespace BlockFeatureLift

variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def largeSubsets (s : Finset V) : Finset (Finset V) :=
  s.powerset.filter fun a => 2 ≤ a.card

omit [Fintype V] in
theorem largeSubsets_card (s : Finset V) :
    (largeSubsets s).card = 2 ^ s.card - s.card - 1 := by
  classical
  have hsmall : s.powerset.filter (fun a => ¬2 ≤ a.card) =
      insert ∅ (s.image fun i => {i}) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · rintro ⟨has, ha⟩
      by_cases hzero : a.card = 0
      · exact Or.inl (Finset.card_eq_zero.mp hzero)
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (by omega : a.card = 1)
        exact Or.inr ⟨i, has (by simp), rfl⟩
    · rintro (rfl | ⟨i, hi, rfl⟩) <;> simp_all
  have hcount := Finset.card_filter_add_card_filter_not (s := s.powerset)
    (fun a : Finset V => 2 ≤ a.card)
  rw [hsmall, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_injective h),
    Finset.card_powerset] at hcount
  change (largeSubsets s).card + (s.card + 1) = 2 ^ s.card at hcount
  omega

def fiber (block : V → B) (b : B) : Finset V :=
  Finset.univ.filter fun i => block i = b

theorem hidden_card_le (block : V → B) :
    Fintype.card (Hidden block) ≤
      ∑ b : B, (2 ^ (fiber block b).card - (fiber block b).card - 1) := by
  classical
  have hset : Finset.univ.filter (fun s : Finset V =>
      2 ≤ s.card ∧ InOneBlock block s) =
      Finset.univ.biUnion (fun b : B => largeSubsets (fiber block b)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, largeSubsets, Finset.mem_powerset]
    constructor
    · rintro ⟨hsize, b, hb⟩
      exact ⟨b, (fun i hi => by simp [fiber, hb i hi]), hsize⟩
    · rintro ⟨b, hs, hsize⟩
      exact ⟨hsize, b, fun i hi => (Finset.mem_filter.mp (hs hi)).2⟩
  calc
    Fintype.card (Hidden block) = _ := Fintype.card_subtype _
    _ = _ := congrArg Finset.card hset
    _ ≤ ∑ b : B, (largeSubsets (fiber block b)).card := Finset.card_biUnion_le
    _ = _ := by simp_rw [largeSubsets_card]

theorem localizationComplexity_le_blockSum (block : V → B) {k : Nat}
    (hk : 2 ≤ k) (hblocks : Fintype.card B ≤ k) (p : Distribution (Assignment V)) :
    localizationComplexity k V p ≤
      ∑ b : B, (2 ^ (fiber block b).card - (fiber block b).card - 1) := by
  have hw := (localization block hk hblocks p).reindex (Equiv.refl V)
    (Fintype.equivFin (Hidden block))
  have hloc : HasKLocalization k (Fintype.card (Hidden block)) V p := by
    refine ⟨?_⟩
    convert hw using 1
    exact (PMF.map_id p).symm
  exact (localizationComplexity_min k V p _ hloc).trans (hidden_card_le block)

end BlockFeatureLift

/-- Balanced block sizes, including empty blocks when `n < k`. -/
def balancedBlockSize (n k : Nat) (b : Fin k) : Nat :=
  n / k + if b.val < n % k then 1 else 0

def BalancedVariables (n k : Nat) := (b : Fin k) × Fin (balancedBlockSize n k b)

instance (n k : Nat) : Fintype (BalancedVariables n k) := inferInstanceAs (Fintype (Sigma _))
instance (n k : Nat) : DecidableEq (BalancedVariables n k) := Classical.decEq _

theorem sum_balancedBlockSize (n k : Nat) (hk : 0 < k) :
    ∑ b : Fin k, balancedBlockSize n k b = n := by
  have hr : n % k < k := Nat.mod_lt n hk
  have hfilter : (Finset.univ.filter (fun b : Fin k => b.val < n % k)).card = n % k := by
    have heq : Finset.univ.filter (fun b : Fin k => b.val < n % k) =
        Finset.Iio (⟨n % k, hr⟩ : Fin k) := by ext b; simp [Fin.lt_def]
    rw [heq, Fin.card_Iio]
  simp only [balancedBlockSize, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_boole]
  rw [hfilter]
  exact Nat.div_add_mod n k

theorem balancedVariables_card (n k : Nat) (hk : 0 < k) :
    Fintype.card (BalancedVariables n k) = n := by
  change Fintype.card (Sigma _) = n
  simpa using sum_balancedBlockSize n k hk

/-- The exact latent bound in the manuscript, with natural-number subtraction. -/
def balancedLiftBound (n k : Nat) : Nat :=
  (n % k) * 2 ^ (n / k + 1) + (k - n % k) * 2 ^ (n / k) - n - k

theorem balanced_feature_sum (n k : Nat) (hk : 0 < k) :
    (∑ b : Fin k, (2 ^ balancedBlockSize n k b - balancedBlockSize n k b - 1)) =
      balancedLiftBound n k := by
  classical
  have hr := Nat.mod_lt n hk
  have hc : (Finset.univ.filter (fun b : Fin k => b.val < n % k)).card = n % k := by
    have heq : Finset.univ.filter (fun b : Fin k => b.val < n % k) =
        Finset.Iio (⟨n % k, hr⟩ : Fin k) := by ext b; simp [Fin.lt_def]
    rw [heq, Fin.card_Iio]
  have hnc : (Finset.univ.filter (fun b : Fin k => ¬b.val < n % k)).card = k - n % k := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun b : Fin k => b.val < n % k)
    simp only [Finset.card_univ, Fintype.card_fin, hc] at h
    omega
  have hpow : (∑ b : Fin k, 2 ^ balancedBlockSize n k b) =
      (n % k) * 2 ^ (n / k + 1) + (k - n % k) * 2 ^ (n / k) := by
    have hterm : ∀ b : Fin k, 2 ^ balancedBlockSize n k b =
        if b.val < n % k then 2 ^ (n / k + 1) else 2 ^ (n / k) := by
      intro b
      split_ifs <;> simp_all [balancedBlockSize]
    simp_rw [hterm]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, hc, hnc, Nat.cast_id]
  have hterm : ∀ b : Fin k,
      (2 ^ balancedBlockSize n k b - balancedBlockSize n k b - 1) +
        balancedBlockSize n k b + 1 = 2 ^ balancedBlockSize n k b := by
    intro b
    have := (balancedBlockSize n k b).lt_two_pow_self
    omega
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun b _ => hterm b)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sum_balancedBlockSize n k hk, hpow] at hsum
  unfold balancedLiftBound
  norm_cast at hsum
  omega

theorem balanced_fiber_card (n k : Nat) (b : Fin k) :
    (BlockFeatureLift.fiber (fun v : BalancedVariables n k => v.fst) b).card =
      balancedBlockSize n k b := by
  classical
  let emb : Fin (balancedBlockSize n k b) ↪ BalancedVariables n k :=
    ⟨fun i => ⟨b, i⟩, fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
  have heq : BlockFeatureLift.fiber (fun v : BalancedVariables n k => v.fst) b =
      Finset.univ.map emb := by
    ext v
    obtain ⟨a, i⟩ := v
    simp only [BlockFeatureLift.fiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map]
    constructor
    · intro hab
      subst a
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (congrArg Sigma.fst hj).symm
  rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- **Theorem `thm:universal-lift`.** The balanced dictionary realizes every
probability table with the exact manuscript latent bound. -/
theorem localizationComplexity_le_balancedLiftBound
    (n k : Nat) (hk : 2 ≤ k) (p : Distribution (BitVec n)) :
    localizationComplexityBits k n p ≤ balancedLiftBound n k := by
  classical
  let V := BalancedVariables n k
  let block : V → Fin k := Sigma.fst
  let ev : V ≃ Fin n := (Fintype.equivFin V).trans
    (finCongr (balancedVariables_card n k (by omega)))
  let source := reindexDistribution ev.symm p
  let loc := (BlockFeatureLift.localization block hk (by simp) source).reindex
    ev (Fintype.equivFin (BlockFeatureLift.Hidden block))
  have hloc : HasKLocalization k (Fintype.card (BlockFeatureLift.Hidden block)) (Fin n) p := by
    refine ⟨?_⟩
    simpa [source] using loc
  have hmin := localizationComplexity_min k (Fin n) p _ hloc
  have hcount := BlockFeatureLift.hidden_card_le block
  have hsum : (∑ b : Fin k, (2 ^ (BlockFeatureLift.fiber block b).card -
      (BlockFeatureLift.fiber block b).card - 1)) = balancedLiftBound n k := by
    have hc : ∀ b : Fin k, (BlockFeatureLift.fiber block b).card =
        balancedBlockSize n k b := fun b => balanced_fiber_card n k b
    simp_rw [hc]
    exact balanced_feature_sum n k (by omega)
  rw [hsum] at hcount
  exact hmin.trans hcount

theorem localizationComplexity_le_min_supportCard_balancedLiftBound
    (n k : Nat) (hk : 2 ≤ k) (p : Distribution (BitVec n)) :
    localizationComplexityBits k n p ≤
      min (UniversalExistence.supportFinset p).card (balancedLiftBound n k) := by
  exact le_min (localizationComplexity_le_supportCard p hk)
    (localizationComplexity_le_balancedLiftBound n k hk p)

theorem balancedLiftBound_le_exponential (n k : Nat) (hk : 0 < k) :
    balancedLiftBound n k ≤ 2 * k * 2 ^ (n / k) := by
  have hr := Nat.mod_lt n hk
  have hdiff : k - n % k + n % k = k := Nat.sub_add_cancel hr.le
  have hp : 0 ≤ 2 ^ (n / k) := Nat.zero_le _
  unfold balancedLiftBound
  calc
    _ ≤ (n % k) * 2 ^ (n / k + 1) + (k - n % k) * 2 ^ (n / k) :=
      (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    _ ≤ _ := by rw [pow_succ]; nlinarith

/-- The uniform finite bound yields the paper's `O_k(2^(n/k))` statement
for every sequence of visible probability tables. -/
theorem localizationComplexity_isBigO_exp
    (k : Nat) (hk : 2 ≤ k) (p : ∀ n, Distribution (BitVec n)) :
    (fun n : Nat => (localizationComplexityBits k n (p n) : ℝ)) =O[Filter.atTop]
      (fun n : Nat => (2 : ℝ) ^ ((n : ℝ) / (k : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound (2 * (k : ℝ))
  apply Filter.Eventually.of_forall
  intro n
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hb := (localizationComplexity_le_balancedLiftBound n k hk (p n)).trans
    (balancedLiftBound_le_exponential n k (by omega))
  have hcast : (localizationComplexityBits k n (p n) : ℝ) ≤
      2 * (k : ℝ) * (2 : ℝ) ^ (n / k) := by exact_mod_cast hb
  apply hcast.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) Nat.cast_div_le

end
end KLocality
