import KLocality.QuadraticFeaturePolynomial

namespace KLocality

open scoped BigOperators

noncomputable section

namespace BlockFeatureLift

variable {V B : Type*} [Fintype V] [DecidableEq V]

/-- A scope lies in one block of the partition. -/
def InOneBlock (block : V → B) (s : Finset V) : Prop :=
  ∃ b, ∀ i ∈ s, block i = b

/-- Exactly the nonsingleton within-block features are charged as hidden bits. -/
def Hidden (block : V → B) :=
  {s : Finset V // 2 ≤ s.card ∧ InOneBlock block s}

instance (block : V → B) : Fintype (Hidden block) := by
  classical
  unfold Hidden
  infer_instance

instance (block : V → B) : DecidableEq (Hidden block) := Classical.decEq _

def lift (block : V → B) (x : Assignment V) : Assignment (V ⊕ Hidden block)
  | .inl i => x i
  | .inr s => decide (s.val ⊆ trueCoordinates x)

@[simp] theorem project_lift (block : V → B) (x : Assignment V) :
    projectObs (lift block x) = x := rfl

theorem lift_injective (block : V → B) : Function.Injective (lift block) := by
  intro x y h
  exact congrArg projectObs h

/-- A nonempty feature is either an existing visible singleton or a hidden coordinate. -/
def coordinate (block : V → B) (s : Finset V) (hne : s.Nonempty)
    (hblock : InOneBlock block s) : V ⊕ Hidden block :=
  if h : s.card = 1 then .inl hne.choose
  else .inr ⟨s, by have := hne.card_pos; omega, hblock⟩

theorem coordinate_lift (block : V → B) (s : Finset V) (hne : s.Nonempty)
    (hblock : InOneBlock block s) (x : Assignment V) :
    lift block x (coordinate block s hne hblock) = decide (s ⊆ trueCoordinates x) := by
  classical
  unfold coordinate
  split_ifs with h
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    have hc : hne.choose = i := by simpa [hi] using hne.choose_spec
    change x hne.choose = _
    rw [hc]
    simp [hi]
  · rfl

def first (block : V → B) (s : Hidden block) : V :=
  (Finset.card_pos.mp (by have := s.property.1; omega : 0 < s.val.card)).choose

omit [Fintype V] [DecidableEq V] in
theorem first_mem (block : V → B) (s : Hidden block) : first block s ∈ s.val :=
  (Finset.card_pos.mp (by have := s.property.1; omega : 0 < s.val.card)).choose_spec

omit [Fintype V] in
theorem rest_nonempty (block : V → B) (s : Hidden block) :
    (s.val.erase (first block s)).Nonempty := by
  have hcard := Finset.card_erase_of_mem (first_mem block s)
  have := s.property.1
  apply Finset.card_pos.mp
  omega

omit [Fintype V] in
theorem rest_inOneBlock (block : V → B) (s : Hidden block) :
    InOneBlock block (s.val.erase (first block s)) := by
  obtain ⟨b, hb⟩ := s.property.2
  exact ⟨b, fun i hi => hb i (Finset.mem_of_mem_erase hi)⟩

def rest (block : V → B) (s : Hidden block) : V ⊕ Hidden block :=
  coordinate block _ (rest_nonempty block s) (rest_inOneBlock block s)

open QuadraticNAND

/-- The Rosenberg AND penalty, with no auxiliary coordinates beyond the dictionary. -/
def penalty (block : V → B) (s : Hidden block) : QuadraticPolynomial (V ⊕ Hidden block) :=
  [.pair 1 (rest block s) (.inl (first block s)),
   .pair (-2) (rest block s) (.inr s),
   .pair (-2) (.inl (first block s)) (.inr s),
   .linear 3 (.inr s)]

omit [Fintype V] in
theorem penalty_nonneg (block : V → B) (s : Hidden block)
    (z : Assignment (V ⊕ Hidden block)) : 0 ≤ (penalty block s).eval z := by
  cases ha : z (rest block s) <;>
    cases hb : z (.inl (first block s)) <;> cases hc : z (.inr s) <;>
    norm_num [penalty, QuadraticPolynomial.eval, QuadraticTerm.eval, bitInt, ha, hb, hc]

omit [Fintype V] in
theorem penalty_zero_iff (block : V → B) (s : Hidden block)
    (z : Assignment (V ⊕ Hidden block)) :
    (penalty block s).eval z = 0 ↔
      z (.inr s) = (z (rest block s) && z (.inl (first block s))) := by
  cases ha : z (rest block s) <;>
    cases hb : z (.inl (first block s)) <;> cases hc : z (.inr s) <;>
    norm_num [penalty, QuadraticPolynomial.eval, QuadraticTerm.eval, bitInt, ha, hb, hc]

theorem penalty_lift (block : V → B) (s : Hidden block) (x : Assignment V) :
    (penalty block s).eval (lift block x) = 0 := by
  rw [penalty_zero_iff]
  change decide (s.val ⊆ trueCoordinates x) =
    (lift block x (coordinate block _ _ _) && x (first block s))
  rw [coordinate_lift]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨fun _ hi => h (Finset.mem_of_mem_erase hi),
      (mem_trueCoordinates x _).mp (h (first_mem block s))⟩
  · rintro ⟨hrest, hfirst⟩ i hi
    by_cases heq : i = first block s
    · simpa [heq] using hfirst
    · exact hrest (Finset.mem_erase.mpr ⟨heq, hi⟩)

/-- Induction by scope size proves uniqueness of the entire feature graph. -/
theorem eq_lift_of_penalties_zero (block : V → B) (z : Assignment (V ⊕ Hidden block))
    (hz : ∀ s, (penalty block s).eval z = 0) : z = lift block (projectObs z) := by
  have hcoord : ∀ n, ∀ (s : Finset V) (hne : s.Nonempty)
      (hb : InOneBlock block s), s.card = n →
      z (coordinate block s hne hb) = decide (s ⊆ trueCoordinates (projectObs z)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hne hb hcard
      by_cases hone : s.card = 1
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
        have hc : hne.choose = i := by simpa [hi] using hne.choose_spec
        rw [coordinate, dif_pos hone, hc]
        simp [hi, projectObs]
      · have htwo : 2 ≤ s.card := by have := hne.card_pos; omega
        let a : Hidden block := ⟨s, htwo, hb⟩
        have hstep := (penalty_zero_iff block a z).mp (hz a)
        have hsmall : (s.erase (first block a)).card < n := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem (first_mem block a)
        have hrest := ih _ hsmall _ (rest_nonempty block a)
          (rest_inOneBlock block a) rfl
        change z (rest block a) = _ at hrest
        rw [hrest] at hstep
        have hlift := (penalty_zero_iff block a (lift block (projectObs z))).mp
          (penalty_lift block a (projectObs z))
        change decide (s ⊆ trueCoordinates (projectObs z)) =
          (lift block (projectObs z) (coordinate block _ _ _) && z (.inl (first block a)))
          at hlift
        rw [coordinate_lift] at hlift
        simpa [coordinate, hone, a] using hstep.trans hlift.symm
  funext i
  cases i with
  | inl i => rfl
  | inr a =>
    have hne : a.val.Nonempty := Finset.card_pos.mp (by have := a.property.1; omega)
    have hone : a.val.card ≠ 1 := by have := a.property.1; omega
    have h := hcoord a.val.card a.val hne a.property.2 rfl
    simpa [coordinate, hone, lift] using h

variable [Fintype B] [DecidableEq B]

def piece (block : V → B) (s : Finset V) (b : B) : Finset V :=
  s.filter fun i => block i = b

omit [Fintype V] [DecidableEq V] [Fintype B] in
theorem piece_inOneBlock (block : V → B) (s : Finset V) (b : B) :
    InOneBlock block (piece block s b) :=
  ⟨b, fun _ hi => (Finset.mem_filter.mp hi).2⟩

def Active (block : V → B) (s : Finset V) := {b : B // (piece block s b).Nonempty}

instance (block : V → B) (s : Finset V) : Fintype (Active block s) := by
  classical
  unfold Active
  infer_instance

def packed (block : V → B) (s : Finset V) : Finset (V ⊕ Hidden block) := by
  classical
  exact Finset.univ.image fun b : Active block s =>
    coordinate block (piece block s b.val) b.property (piece_inOneBlock block s b.val)

omit [Fintype V] in
theorem packed_card_le (block : V → B) (s : Finset V) :
    (packed block s).card ≤ Fintype.card B := by
  classical
  exact (Finset.card_image_le).trans (by
    simpa using (Fintype.card_subtype_le (fun b => (piece block s b).Nonempty)))

/-- Every visible monomial uses at most one feature from each block. -/
theorem monomial_packed_lift (block : V → B) (s : Finset V) (x : Assignment V) :
    monomialValue (packed block s) (lift block x) = monomialValue s x := by
  classical
  have hiff : packed block s ⊆ trueCoordinates (lift block x) ↔
      s ⊆ trueCoordinates x := by
    constructor
    · intro h i hi
      have hne : (piece block s (block i)).Nonempty := ⟨i, by simp [piece, hi]⟩
      let b : Active block s := ⟨block i, hne⟩
      have hc : coordinate block (piece block s b.val) b.property
          (piece_inOneBlock block s b.val) ∈ packed block s :=
        Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
      have htrue := (mem_trueCoordinates _ _).mp (h hc)
      rw [coordinate_lift, decide_eq_true_eq] at htrue
      exact htrue (by simp [b, piece, hi])
    · intro h c hc
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hc
      rw [mem_trueCoordinates, coordinate_lift, decide_eq_true_eq]
      exact fun _ hi => h (Finset.mem_filter.mp hi).1
  unfold monomialValue
  simp only [hiff]

def lifted (block : V → B) (p : Distribution (Assignment V)) :
    Distribution (Assignment (V ⊕ Hidden block)) := p.map (lift block)

omit [Fintype B] [DecidableEq B] in
theorem lifted_marginal (block : V → B) (p : Distribution (Assignment V)) :
    IsMarginalModel p (lifted block p) := by
  unfold IsMarginalModel lifted
  rw [PMF.map_comp]
  exact PMF.map_id p

omit [Fintype B] [DecidableEq B] in
theorem support_graph_of_sameMoments (block : V → B) {k : Nat} (hk : 2 ≤ k)
    (p : Distribution (Assignment V)) (q : Distribution (Assignment (V ⊕ Hidden block)))
    (hm : SameFeatureMomentsUpTo k (lifted block p) q) :
    ∀ z ∈ q.support, z = lift block (projectObs z) := by
  intro z hz
  apply eq_lift_of_penalties_zero
  intro s
  let e := (penalty block s).toFeaturePolynomial
  have hm2 : SameFeatureMomentsUpTo 2 (lifted block p) q :=
    fun scope hscope => hm scope (hscope.trans hk)
  have hp : pmfExpectation (lifted block p) e.eval = 0 := by
    rw [lifted, pmfExpectation_map]
    have hzero : (fun x => e.eval (lift block x)) = fun _ => 0 := by
      funext x
      simp [e, penalty_lift]
    rw [hzero, pmfExpectation_zero]
  have hq : pmfExpectation q e.eval = 0 := by
    rw [e.expectation_eval_eq_of_sameFeatureMoments hm2, hp]
  have hnonneg : ∀ y, 0 ≤ e.eval y := by
    intro y
    simp only [e, QuadraticPolynomial.eval_toFeaturePolynomial]
    exact_mod_cast penalty_nonneg block s y
  have h := support_subset_zeroSet_of_pmfExpectation_eq_zero q e.eval hnonneg hq hz
  simpa [e] using h

theorem expectation_congr_support {A : Type*} [Fintype A]
    (p : Distribution A) (f g : A → ℝ) (h : ∀ x ∈ p.support, f x = g x) :
    pmfExpectation p f = pmfExpectation p g := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x = 0
  · simp [hx]
  · rw [h x ((PMF.mem_support_iff p x).mpr hx)]

theorem map_congr_support {A C : Type*} (p : Distribution A) (f g : A → C)
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  classical
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · rw [h x ((PMF.mem_support_iff p x).mpr hx)]

/-- The graph and the packed moments determine the joint law, for arbitrary target weights. -/
theorem eq_lifted_of_sameMoments (block : V → B) {k : Nat}
    (hk : 2 ≤ k) (hblocks : Fintype.card B ≤ k)
    (p : Distribution (Assignment V)) (q : Distribution (Assignment (V ⊕ Hidden block)))
    (hm : SameFeatureMomentsUpTo k (lifted block p) q) : q = lifted block p := by
  have hgraph := support_graph_of_sameMoments block hk p q hm
  have hmarg : q.map projectObs = p := by
    apply distribution_eq_of_monomialMoments_eq
    intro s
    have hpacked := hm (packed block s) ((packed_card_le block s).trans hblocks)
    simp only [monomialMoment_eq_expectation] at hpacked ⊢
    rw [lifted, pmfExpectation_map] at hpacked
    simp_rw [monomial_packed_lift] at hpacked
    rw [pmfExpectation_map, ← hpacked]
    apply expectation_congr_support
    intro z hz
    conv_rhs => rw [hgraph z hz]
    exact (monomial_packed_lift block s (projectObs z)).symm
  have hback : (q.map projectObs).map (lift block) = q := by
    rw [PMF.map_comp]
    calc
      q.map (lift block ∘ projectObs) = q.map id :=
        map_congr_support q _ _ (fun z hz => (hgraph z hz).symm)
      _ = q := PMF.map_id q
  rw [hmarg] at hback
  exact hback.symm

/-- Universal locality for any partition into at most `k` blocks. -/
theorem lifted_isKLocal (block : V → B) {k : Nat}
    (hk : 2 ≤ k) (hblocks : Fintype.card B ≤ k) (p : Distribution (Assignment V)) :
    IsKLocalMarginal k (lifted block p) := by
  apply (isKLocalMarginal_iff_maxEntropy_sameFeatureMoments k _).mpr
  refine ⟨fun _ _ => rfl, ?_⟩
  intro q hq
  rw [eq_lifted_of_sameMoments block hk hblocks p q hq]

/-- The lift as a witness, with the hidden type still exposing the feature dictionary. -/
def localization (block : V → B) {k : Nat}
    (hk : 2 ≤ k) (hblocks : Fintype.card B ≤ k) (p : Distribution (Assignment V)) :
    KLocalization k V (Hidden block) p where
  lifted := lifted block p
  marginal := lifted_marginal block p
  kLocal := lifted_isKLocal block hk hblocks p

end BlockFeatureLift
end
end KLocality
