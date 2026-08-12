import KLocality.Tactic

namespace KLocality

open scoped BigOperators

universe u

/-!
# Universal localization existence

This file formalizes Proposition `prop:existence` from `main.tex`.  The
construction assigns one latent bit to every point in the visible support,
uses a quadratic exact-one penalty, and forces an active latent bit to agree
with its associated visible point.  Unary hidden marginals retain the
arbitrary (not necessarily uniform) support weights.
-/

namespace UniversalExistence

open QuadraticNAND
open Tactic

/-- The finite support of a PMF, represented as a finset. -/
noncomputable def supportFinset
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) : Finset (Assignment ObsVar) :=
  Finset.univ.filter fun x => p x ≠ 0

@[simp]
theorem mem_supportFinset
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (x : Assignment ObsVar) :
    x ∈ supportFinset p ↔ x ∈ p.support := by
  simp [supportFinset, PMF.mem_support_iff]

theorem supportFinset_nonempty
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    (supportFinset p).Nonempty := by
  rcases p.support_nonempty with ⟨x, hx⟩
  exact ⟨x, (mem_supportFinset p x).2 hx⟩

/-- One latent coordinate for each visible support point. -/
abbrev SupportIndex
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :=
  Fin (supportFinset p).card

/-- Decode a latent coordinate to its associated visible support point. -/
noncomputable def supportPoint
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (j : SupportIndex p) :
    Assignment ObsVar :=
  ((Finset.equivFin (supportFinset p)).symm j).1

theorem supportPoint_mem
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (j : SupportIndex p) :
    supportPoint p j ∈ supportFinset p :=
  ((Finset.equivFin (supportFinset p)).symm j).2

theorem supportPoint_injective
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    Function.Injective (supportPoint p) := by
  intro i j hij
  apply (Finset.equivFin (supportFinset p)).symm.injective
  apply Subtype.ext
  exact hij

theorem exists_unique_supportPoint
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    {x : Assignment ObsVar} (hx : x ∈ supportFinset p) :
    ∃! j : SupportIndex p, supportPoint p j = x := by
  let sx : ↥(supportFinset p) := ⟨x, hx⟩
  refine ⟨Finset.equivFin (supportFinset p) sx, ?_, ?_⟩
  · exact congrArg Subtype.val ((Finset.equivFin (supportFinset p)).symm_apply_apply sx)
  · intro j hj
    have hChosen : supportPoint p (Finset.equivFin (supportFinset p) sx) = x :=
      congrArg Subtype.val ((Finset.equivFin (supportFinset p)).symm_apply_apply sx)
    exact supportPoint_injective p (hj.trans hChosen.symm)

/-- The canonical lifted assignment: visible coordinates are unchanged and
exactly the bit indexed by the visible support point is active.  Outside the
support all latent bits are false, but those inputs have zero `p`-mass. -/
noncomputable def liftAssignment
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (x : Assignment ObsVar) :
    Assignment (Sum ObsVar (SupportIndex p)) :=
  fun
  | Sum.inl i => x i
  | Sum.inr j => decide (x = supportPoint p j)

@[simp]
theorem liftAssignment_observed
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (x : Assignment ObsVar) (i : ObsVar) :
    liftAssignment p x (Sum.inl i) = x i :=
  rfl

@[simp]
theorem liftAssignment_latent
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (x : Assignment ObsVar)
    (j : SupportIndex p) :
    liftAssignment p x (Sum.inr j) = decide (x = supportPoint p j) :=
  rfl

@[simp]
theorem liftAssignment_latent_eq_true_iff
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (x : Assignment ObsVar)
    (j : SupportIndex p) :
    liftAssignment p x (Sum.inr j) = true ↔ x = supportPoint p j := by
  simp [liftAssignment]

theorem liftAssignment_injective
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    Function.Injective (liftAssignment p) := by
  intro x y hxy
  funext i
  exact congrFun hxy (Sum.inl i)

/-- The arbitrary-weight lifted law supported on the one-hot graph. -/
noncomputable def lifted
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    Distribution (Assignment (Sum ObsVar (SupportIndex p))) :=
  p.map (liftAssignment p)

theorem lifted_isMarginalModel
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    IsMarginalModel p (lifted p) := by
  unfold IsMarginalModel lifted
  rw [PMF.map_comp]
  convert PMF.map_id p using 1

/-- The integer number of active support-index bits. -/
noncomputable def activeCount
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {p : Distribution (Assignment ObsVar)}
    (z : Assignment (Sum ObsVar (SupportIndex p))) : ℤ :=
  ∑ j : SupportIndex p, QuadraticNAND.bitInt (z (Sum.inr j))

/-- The finite set of active support-index bits. -/
noncomputable def activeIndices
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {p : Distribution (Assignment ObsVar)}
    (z : Assignment (Sum ObsVar (SupportIndex p))) : Finset (SupportIndex p) :=
  Finset.univ.filter fun j => z (Sum.inr j) = true

@[simp]
theorem mem_activeIndices
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {p : Distribution (Assignment ObsVar)}
    (z : Assignment (Sum ObsVar (SupportIndex p))) (j : SupportIndex p) :
    j ∈ activeIndices z ↔ z (Sum.inr j) = true := by
  simp [activeIndices]

theorem activeCount_eq_card_activeIndices
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {p : Distribution (Assignment ObsVar)}
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    activeCount z = ((activeIndices z).card : ℤ) := by
  classical
  simp [activeCount, activeIndices, QuadraticNAND.bitInt]

/-- The syntactically quadratic expansion of `(sum_j h_j - 1)^2`.

The pair sum is over all ordered pairs, including the diagonal.  On Boolean
inputs it evaluates to the square of the active-bit count. -/
noncomputable def exactOnePolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    QuadraticPolynomial (Sum ObsVar (SupportIndex p)) :=
  [.constant 1] ++
    (Finset.univ.toList.map fun j : SupportIndex p =>
      QuadraticTerm.linear (-2) (Sum.inr j)) ++
    ((Finset.univ ×ˢ Finset.univ).toList.map fun pair : SupportIndex p × SupportIndex p =>
      QuadraticTerm.pair 1 (Sum.inr pair.1) (Sum.inr pair.2))

theorem eval_exactOnePolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (exactOnePolynomial p).eval z = (activeCount z - 1) ^ 2 := by
  classical
  simp [exactOnePolynomial, QuadraticPolynomial.eval, activeCount]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

theorem eval_exactOnePolynomial_nonneg
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    0 ≤ (exactOnePolynomial p).eval z := by
  rw [eval_exactOnePolynomial]
  positivity

theorem eval_exactOnePolynomial_eq_zero_iff
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (exactOnePolynomial p).eval z = 0 ↔
      ∃! j : SupportIndex p, z (Sum.inr j) = true := by
  classical
  rw [eval_exactOnePolynomial]
  constructor
  · intro hzero
    have hcount : activeCount z = 1 := by
      nlinarith [sq_nonneg (activeCount z - 1)]
    have hcard : (activeIndices z).card = 1 := by
      rw [activeCount_eq_card_activeIndices] at hcount
      exact_mod_cast hcount
    rcases Finset.card_eq_one.mp hcard with ⟨j, hj⟩
    refine ⟨j, ?_, ?_⟩
    · exact (mem_activeIndices z j).1 (by simp [hj])
    · intro j' hj'
      have hj'mem : j' ∈ activeIndices z := (mem_activeIndices z j').2 hj'
      simpa [hj] using hj'mem
  · rintro ⟨j, hj, hUnique⟩
    have hactive : activeIndices z = {j} := by
      ext j'
      constructor
      · intro hj'mem
        have hj'true := (mem_activeIndices z j').1 hj'mem
        simp [hUnique j' hj'true]
      · intro hj'mem
        have : j' = j := by simpa using hj'mem
        simpa [this] using hj
    rw [activeCount_eq_card_activeIndices, hactive]
    norm_num

/-- Quadratic penalty for an active support bit whose associated visible
coordinate disagrees with the current visible assignment. -/
noncomputable def mismatchPenalty
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (j : SupportIndex p) (i : ObsVar) :
    QuadraticPolynomial (Sum ObsVar (SupportIndex p)) :=
  if supportPoint p j i then
    [QuadraticTerm.linear 1 (Sum.inr j),
      QuadraticTerm.pair (-1) (Sum.inr j) (Sum.inl i)]
  else
    [QuadraticTerm.pair 1 (Sum.inr j) (Sum.inl i)]

theorem eval_mismatchPenalty
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (j : SupportIndex p) (i : ObsVar)
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (mismatchPenalty p j i).eval z =
      if z (Sum.inr j) = true ∧ z (Sum.inl i) ≠ supportPoint p j i then 1 else 0 := by
  classical
  cases hTarget : supportPoint p j i <;>
    cases hHidden : z (Sum.inr j) <;>
    cases hVisible : z (Sum.inl i) <;>
    simp [mismatchPenalty, hTarget, hHidden, hVisible, QuadraticPolynomial.eval,
      QuadraticNAND.bitInt]

/-- Sum of all hidden-to-visible consistency penalties. -/
noncomputable def consistencyPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    QuadraticPolynomial (Sum ObsVar (SupportIndex p)) :=
  (Finset.univ.toList : List (SupportIndex p × ObsVar)).flatMap fun pair =>
    mismatchPenalty p pair.1 pair.2

theorem eval_consistencyPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (consistencyPolynomial p).eval z =
      ∑ pair : SupportIndex p × ObsVar,
        if z (Sum.inr pair.1) = true ∧
            z (Sum.inl pair.2) ≠ supportPoint p pair.1 pair.2 then 1 else 0 := by
  classical
  simp [consistencyPolynomial, eval_mismatchPenalty]

theorem eval_consistencyPolynomial_nonneg
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    0 ≤ (consistencyPolynomial p).eval z := by
  rw [eval_consistencyPolynomial]
  positivity

theorem eval_consistencyPolynomial_eq_zero_iff
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (consistencyPolynomial p).eval z = 0 ↔
      ∀ j : SupportIndex p, z (Sum.inr j) = true →
        ∀ i : ObsVar, z (Sum.inl i) = supportPoint p j i := by
  classical
  rw [eval_consistencyPolynomial]
  have hNonneg : ∀ pair : SupportIndex p × ObsVar,
      0 ≤ (if z (Sum.inr pair.1) = true ∧
          z (Sum.inl pair.2) ≠ supportPoint p pair.1 pair.2 then (1 : ℤ) else 0) := by
    intro pair
    split <;> norm_num
  constructor
  · intro hsum j hj i
    have hzero := (Fintype.sum_eq_zero_iff_of_nonneg hNonneg).1 hsum
    have hpair :
        (if z (Sum.inr j) = true ∧ z (Sum.inl i) ≠ supportPoint p j i
          then (1 : ℤ) else 0) = 0 := by
      exact congrFun hzero (j, i)
    by_contra hne
    simp [hj, hne] at hpair
  · intro h
    apply (Fintype.sum_eq_zero_iff_of_nonneg hNonneg).2
    funext pair
    by_cases hj : z (Sum.inr pair.1) = true
    · have hi := h pair.1 hj pair.2
      simp [hj, hi]
    · simp [hj]

/-- The full quadratic one-hot graph energy. -/
noncomputable def graphPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    QuadraticPolynomial (Sum ObsVar (SupportIndex p)) :=
  exactOnePolynomial p ++ consistencyPolynomial p

theorem eval_graphPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (graphPolynomial p).eval z =
      (exactOnePolynomial p).eval z + (consistencyPolynomial p).eval z := by
  simp [graphPolynomial]

theorem eval_graphPolynomial_nonneg
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    0 ≤ (graphPolynomial p).eval z := by
  rw [eval_graphPolynomial]
  exact add_nonneg (eval_exactOnePolynomial_nonneg p z)
    (eval_consistencyPolynomial_nonneg p z)

theorem eval_graphPolynomial_eq_zero_iff
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (graphPolynomial p).eval z = 0 ↔
      ∃ x ∈ supportFinset p, z = liftAssignment p x := by
  classical
  constructor
  · intro hzero
    have hExactNonneg := eval_exactOnePolynomial_nonneg p z
    have hConsistencyNonneg := eval_consistencyPolynomial_nonneg p z
    have hsum : (exactOnePolynomial p).eval z +
        (consistencyPolynomial p).eval z = 0 := by
      simpa [eval_graphPolynomial] using hzero
    have hExactZero : (exactOnePolynomial p).eval z = 0 := by omega
    have hConsistencyZero : (consistencyPolynomial p).eval z = 0 := by omega
    rcases (eval_exactOnePolynomial_eq_zero_iff p z).1 hExactZero with
      ⟨j, hj, hUnique⟩
    have hAgrees := (eval_consistencyPolynomial_eq_zero_iff p z).1 hConsistencyZero
    refine ⟨supportPoint p j, supportPoint_mem p j, ?_⟩
    funext coordinate
    cases coordinate with
    | inl i =>
        simpa using hAgrees j hj i
    | inr j' =>
        by_cases hj' : j' = j
        · subst j'
          simp [hj]
        · have hPointNe : supportPoint p j ≠ supportPoint p j' := by
            intro hPoints
            exact hj' (supportPoint_injective p hPoints.symm)
          cases hbit : z (Sum.inr j') with
          | false => simp [liftAssignment, hPointNe]
          | true =>
              have : j' = j := hUnique j' hbit
              exact (hj' this).elim
  · rintro ⟨x, hx, rfl⟩
    rcases exists_unique_supportPoint p hx with ⟨j, hj, hUnique⟩
    have hExactZero :
        (exactOnePolynomial p).eval (liftAssignment p x) = 0 := by
      apply (eval_exactOnePolynomial_eq_zero_iff p (liftAssignment p x)).2
      refine ⟨j, ?_, ?_⟩
      · exact (liftAssignment_latent_eq_true_iff p x j).2 hj.symm
      · intro j' hj'
        exact hUnique j' ((liftAssignment_latent_eq_true_iff p x j').1 hj').symm
    have hConsistencyZero :
        (consistencyPolynomial p).eval (liftAssignment p x) = 0 := by
      apply (eval_consistencyPolynomial_eq_zero_iff p (liftAssignment p x)).2
      intro j' hj' i
      have hxj := (liftAssignment_latent_eq_true_iff p x j').1 hj'
      simp [hxj]
    rw [eval_graphPolynomial, hExactZero, hConsistencyZero, add_zero]

/-- Zero-coefficient unary terms do not change the energy, but their singleton
scopes make every hidden marginal explicitly available among the canonical
local constraints.  Those marginals retain the arbitrary weights of `p`. -/
noncomputable def weightMarkerPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    QuadraticPolynomial (Sum ObsVar (SupportIndex p)) :=
  Finset.univ.toList.map fun j : SupportIndex p =>
    QuadraticTerm.linear 0 (Sum.inr j)

/-- Graph energy together with unary weight-marker scopes. -/
noncomputable def localizationPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    QuadraticPolynomial (Sum ObsVar (SupportIndex p)) :=
  graphPolynomial p ++ weightMarkerPolynomial p

@[simp]
theorem eval_weightMarkerPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (weightMarkerPolynomial p).eval z = 0 := by
  classical
  simp [weightMarkerPolynomial, QuadraticPolynomial.eval]

theorem eval_localizationPolynomial
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (localizationPolynomial p).eval z = (graphPolynomial p).eval z := by
  simp [localizationPolynomial]

theorem eval_localizationPolynomial_nonneg
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    0 ≤ (localizationPolynomial p).eval z := by
  rw [eval_localizationPolynomial]
  exact eval_graphPolynomial_nonneg p z

theorem eval_localizationPolynomial_eq_zero_iff
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    (localizationPolynomial p).eval z = 0 ↔
      ∃ x ∈ supportFinset p, z = liftAssignment p x := by
  rw [eval_localizationPolynomial]
  exact eval_graphPolynomial_eq_zero_iff p z

theorem support_lifted
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    (lifted p).support =
      liftAssignment p '' (supportFinset p : Set (Assignment ObsVar)) := by
  rw [lifted, PMF.support_map]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (mem_supportFinset p x).2 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (mem_supportFinset p x).1 hx, rfl⟩

theorem lifted_support_subset_zeroSet
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    (lifted p).support ⊆
      {z | (localizationPolynomial p).eval z = 0} := by
  intro z hz
  rw [support_lifted] at hz
  rcases hz with ⟨x, hx, rfl⟩
  exact (eval_localizationPolynomial_eq_zero_iff p (liftAssignment p x)).2
    ⟨x, hx, rfl⟩

/-- Scoped real-valued terms used as the marginal certificate. -/
noncomputable def localizationTerms
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    List (LocalEnergyTerm (Sum ObsVar (SupportIndex p))) :=
  (localizationPolynomial p).toLocalEnergy

theorem localizationTerms_respect_two
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    LocalEnergyTermsRespectK 2 (localizationTerms p) := by
  klocality [localizationTerms]

theorem localizationEnergy_nonneg
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (z : Assignment (Sum ObsVar (SupportIndex p))) :
    0 ≤ localEnergyEval (localizationTerms p) z := by
  rw [localizationTerms, QuadraticPolynomial.localEnergyEval_toLocalEnergy]
  exact_mod_cast eval_localizationPolynomial_nonneg p z

theorem lifted_support_subset_localEnergy_zeroSet
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    (lifted p).support ⊆
      {z | localEnergyEval (localizationTerms p) z = 0} := by
  intro z hz
  change localEnergyEval (localizationTerms p) z = 0
  rw [localizationTerms, QuadraticPolynomial.localEnergyEval_toLocalEnergy]
  norm_cast
  exact lifted_support_subset_zeroSet p hz

/-- Every law sharing the certificate marginals is supported on the same
one-hot graph. -/
theorem feasible_support_subset_graph
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (q : Distribution (Assignment (Sum ObsVar (SupportIndex p))))
    (hFeasible : FeasibleMarginals
      (localEnergyConstraints (localizationTerms p) (lifted p)) q) :
    q.support ⊆
      {z | ∃ x ∈ supportFinset p, z = liftAssignment p x} := by
  have hzero := support_subset_zeroSet_of_feasible_localEnergy
    (localizationEnergy_nonneg p)
    (lifted_support_subset_localEnergy_zeroSet p) hFeasible
  intro z hz
  have hzZero := hzero hz
  change localEnergyEval (localizationTerms p) z = 0 at hzZero
  rw [localizationTerms, QuadraticPolynomial.localEnergyEval_toLocalEnergy] at hzZero
  norm_cast at hzZero
  exact (eval_localizationPolynomial_eq_zero_iff p z).1 hzZero

/-- The zero-coefficient unary marker for latent coordinate `j`. -/
noncomputable def weightMarkerTerm
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {p : Distribution (Assignment ObsVar)} (j : SupportIndex p) :
    LocalEnergyTerm (Sum ObsVar (SupportIndex p)) :=
  (QuadraticTerm.linear 0 (Sum.inr j)).toLocalEnergyTerm

theorem weightMarkerTerm_mem
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (j : SupportIndex p) :
    weightMarkerTerm j ∈ localizationTerms p := by
  classical
  simp [weightMarkerTerm, localizationTerms, localizationPolynomial,
    weightMarkerPolynomial, QuadraticPolynomial.toLocalEnergy]

@[simp]
theorem weightMarkerTerm_scope
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {p : Distribution (Assignment ObsVar)} (j : SupportIndex p) :
    (weightMarkerTerm j).scope = {Sum.inr j} :=
  rfl

theorem feasible_weightMarker_marginal
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (q : Distribution (Assignment (Sum ObsVar (SupportIndex p))))
    (hFeasible : FeasibleMarginals
      (localEnergyConstraints (localizationTerms p) (lifted p)) q)
    (j : SupportIndex p) :
    marginal {Sum.inr j} q = marginal {Sum.inr j} (lifted p) := by
  let term := weightMarkerTerm (p := p) j
  have hTerm : term ∈ localizationTerms p := weightMarkerTerm_mem p j
  have hConstraint : term.constraint (lifted p) ∈
      localEnergyConstraints (localizationTerms p) (lifted p) := by
    exact List.mem_map.mpr ⟨term, hTerm, rfl⟩
  simpa [term] using hFeasible (term.constraint (lifted p)) hConstraint

/-- The all-true assignment on the singleton scope containing latent bit `j`. -/
noncomputable def latentTruePattern
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {p : Distribution (Assignment ObsVar)} (j : SupportIndex p) :
    Assignment ({Sum.inr j} : Finset (Sum ObsVar (SupportIndex p))) :=
  fun _ => true

theorem restrict_liftAssignment_eq_latentTruePattern_iff
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (x : Assignment ObsVar) (j : SupportIndex p) :
    restrict {Sum.inr j} (liftAssignment p x) = latentTruePattern j ↔
      x = supportPoint p j := by
  constructor
  · intro h
    have hAt := congrFun h ⟨Sum.inr j, Finset.mem_singleton_self _⟩
    simpa [restrict, latentTruePattern] using
      (liftAssignment_latent_eq_true_iff p x j).1 hAt
  · intro hx
    funext coordinate
    rcases coordinate with ⟨coordinate, hCoordinate⟩
    have : coordinate = Sum.inr j := Finset.mem_singleton.mp hCoordinate
    subst coordinate
    exact (liftAssignment_latent_eq_true_iff p x j).2 hx

/-- On a law supported by the one-hot graph, the mass of the graph point
indexed by `j` is exactly the true cell of the singleton `j`-marginal. -/
theorem apply_liftAssignment_eq_singletonMarginal
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (q : Distribution (Assignment (Sum ObsVar (SupportIndex p))))
    (hSupport : q.support ⊆
      {z | ∃ x ∈ supportFinset p, z = liftAssignment p x})
    (x : Assignment ObsVar)
    (j : SupportIndex p) (hj : supportPoint p j = x) :
    q (liftAssignment p x) =
      marginal {Sum.inr j} q (latentTruePattern j) := by
  rw [marginal, PMF.map_apply]
  rw [tsum_eq_single (liftAssignment p x)]
  · have hPattern :
        latentTruePattern j = restrict {Sum.inr j} (liftAssignment p x) := by
      symm
      exact (restrict_liftAssignment_eq_latentTruePattern_iff p x j).2 hj.symm
    simp [hPattern]
  · intro z hz
    by_cases hzSupport : z ∈ q.support
    · rcases hSupport hzSupport with ⟨y, hy, rfl⟩
      have hyx : y ≠ x := by
        intro hyx
        apply hz
        exact congrArg (liftAssignment p) hyx
      have hPatternNe :
          latentTruePattern j ≠ restrict {Sum.inr j} (liftAssignment p y) := by
        intro hPattern
        have hyPoint : y = supportPoint p j :=
          (restrict_liftAssignment_eq_latentTruePattern_iff p y j).1 hPattern.symm
        exact hyx (hyPoint.trans hj)
      simp [hPatternNe]
    · have hzZero : q z = 0 := (q.apply_eq_zero_iff z).2 hzSupport
      simp [hzZero]

theorem lifted_apply_liftAssignment
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) (x : Assignment ObsVar) :
    lifted p (liftAssignment p x) = p x := by
  rw [lifted, PMF.map_apply]
  rw [tsum_eq_single x]
  · simp
  · intro y hy
    have hLiftNe : liftAssignment p x ≠ liftAssignment p y := by
      intro hLift
      exact hy (liftAssignment_injective p hLift).symm
    simp [hLiftNe]

theorem feasible_apply_liftAssignment
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (q : Distribution (Assignment (Sum ObsVar (SupportIndex p))))
    (hFeasible : FeasibleMarginals
      (localEnergyConstraints (localizationTerms p) (lifted p)) q)
    (x : Assignment ObsVar) (hx : x ∈ supportFinset p) :
    q (liftAssignment p x) = lifted p (liftAssignment p x) := by
  rcases exists_unique_supportPoint p hx with ⟨j, hj, _hUnique⟩
  have hqSupport := feasible_support_subset_graph p q hFeasible
  have hpSupport : (lifted p).support ⊆
      {z | ∃ y ∈ supportFinset p, z = liftAssignment p y} := by
    intro z hz
    rw [support_lifted] at hz
    rcases hz with ⟨y, hy, hyz⟩
    exact ⟨y, hy, hyz.symm⟩
  have hMarginal := feasible_weightMarker_marginal p q hFeasible j
  calc
    q (liftAssignment p x) =
        marginal {Sum.inr j} q (latentTruePattern j) :=
      apply_liftAssignment_eq_singletonMarginal p q hqSupport x j hj
    _ = marginal {Sum.inr j} (lifted p) (latentTruePattern j) := by
      rw [hMarginal]
    _ = lifted p (liftAssignment p x) :=
      (apply_liftAssignment_eq_singletonMarginal p (lifted p) hpSupport x j hj).symm

/-- The quadratic certificate marginals uniquely determine the arbitrary-weight
one-hot lift. -/
theorem feasible_eq_lifted
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar))
    (q : Distribution (Assignment (Sum ObsVar (SupportIndex p))))
    (hFeasible : FeasibleMarginals
      (localEnergyConstraints (localizationTerms p) (lifted p)) q) :
    q = lifted p := by
  apply PMF.ext
  intro z
  by_cases hzGraph : ∃ x ∈ supportFinset p, z = liftAssignment p x
  · rcases hzGraph with ⟨x, hx, rfl⟩
    exact feasible_apply_liftAssignment p q hFeasible x hx
  · have hqNotSupport : z ∉ q.support := by
      intro hz
      exact hzGraph (feasible_support_subset_graph p q hFeasible hz)
    have hpNotSupport : z ∉ (lifted p).support := by
      intro hz
      rw [support_lifted] at hz
      rcases hz with ⟨x, hx, hxz⟩
      exact hzGraph ⟨x, hx, hxz.symm⟩
    rw [(q.apply_eq_zero_iff z).2 hqNotSupport,
      ((lifted p).apply_eq_zero_iff z).2 hpNotSupport]




theorem lifted_isTwoLocal
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    IsKLocalMarginal 2 (lifted p) := by
  apply isKLocalMarginal_of_unique_feasible 2 (lifted p)
      (localEnergyConstraints (localizationTerms p) (lifted p))
  · exact localEnergyConstraints_respectK (lifted p) (localizationTerms_respect_two p)
  · exact feasible_localEnergyConstraints_self (localizationTerms p) (lifted p)
  · intro q hq
    exact feasible_eq_lifted p q hq

/-- The paper's universal one-hot construction as a concrete localization. -/
noncomputable def universalTwoLocalization
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    KLocalization 2 ObsVar (SupportIndex p) p where
  lifted := lifted p
  marginal := lifted_isMarginalModel p
  kLocal := lifted_isTwoLocal p

end UniversalExistence

open UniversalExistence

/-- **Proposition `prop:existence` (existence part).** Every finite Boolean law
has a 2-localization with one latent coordinate per support point. -/
theorem hasTwoLocalization_supportCard
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) :
    HasKLocalization 2 (supportFinset p).card ObsVar p := by
  exact ⟨universalTwoLocalization p⟩

/-- Universal existence at every locality `k ≥ 2`. -/
theorem hasKLocalization_supportCard
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) {k : Nat} (hk : 2 ≤ k) :
    HasKLocalization k (supportFinset p).card ObsVar p :=
  hasKLocalization_mono hk (hasTwoLocalization_supportCard p)

/-- Localization existence is unconditional in the paper's range `k ≥ 2`. -/
theorem kLocalization_exists
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) {k : Nat} (hk : 2 ≤ k) :
    ∃ latentVars, HasKLocalization k latentVars ObsVar p :=
  ⟨(supportFinset p).card, hasKLocalization_supportCard p hk⟩

/-- **Proposition `prop:existence` (support bound).** -/
theorem localizationComplexity_le_supportCard
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) {k : Nat} (hk : 2 ≤ k) :
    localizationComplexity k ObsVar p ≤
      (supportFinset p).card := by
  exact localizationComplexity_min k ObsVar p
    (supportFinset p).card (hasKLocalization_supportCard p hk)

/-- **Proposition `prop:existence` (the full displayed inequality).** -/
theorem localizationComplexity_le_two_le_supportCard
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    (p : Distribution (Assignment ObsVar)) {k : Nat} (hk : 2 ≤ k) :
    localizationComplexity k ObsVar p ≤
        localizationComplexity 2 ObsVar p ∧
      localizationComplexity 2 ObsVar p ≤
        (supportFinset p).card := by
  constructor
  · exact localizationComplexity_mono hk (kLocalization_exists p le_rfl)
  · exact localizationComplexity_le_supportCard p le_rfl

end KLocality
