import KLocality.Tactic

namespace KLocality

open scoped BigOperators

universe u

/-!
# Canonical marginal constraints and Boolean features

This module begins the formal counterpart of Lemma `lem:canonical`.  It first
packages every scope of cardinality at most `k` into one canonical finite list
and proves the entropy-maximization characterization using that list.  The
second part identifies these constraints with the monomial feature moments
used by the paper.
-/

/-- Two laws have the same marginals on every scope of size at most `k`. -/
def SameMarginalsUpTo
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p q : Distribution (Assignment Var)) : Prop :=
  ∀ scope : Finset Var, scope.card ≤ k → marginal scope q = marginal scope p

@[refl]
theorem sameMarginalsUpTo_refl
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    SameMarginalsUpTo k p p := by
  intro scope _
  rfl

/-- The finite list of all variable scopes of cardinality at most `k`. -/
noncomputable def scopesUpTo
    (Var : Type u) [Fintype Var] [DecidableEq Var] (k : Nat) :
    List (Finset Var) :=
  ((Finset.univ : Finset (Finset Var)).filter fun scope => scope.card ≤ k).toList

@[simp]
theorem mem_scopesUpTo
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (scope : Finset Var) :
    scope ∈ scopesUpTo Var k ↔ scope.card ≤ k := by
  classical
  simp [scopesUpTo]

/-- The canonical list fixes the target law's marginal on every scope of
cardinality at most `k`. -/
noncomputable def canonicalMarginalConstraints
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    List (MarginalConstraint Var) :=
  (scopesUpTo Var k).map fun scope =>
    { scope := scope
      target := marginal scope p }

theorem canonicalMarginalConstraints_respectK
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    MarginalConstraintsRespectK k (canonicalMarginalConstraints k p) := by
  classical
  intro constraint hConstraint
  rcases List.mem_map.mp hConstraint with ⟨scope, hScope, rfl⟩
  exact (mem_scopesUpTo k scope).1 hScope

theorem feasible_canonicalMarginalConstraints_iff
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p q : Distribution (Assignment Var)) :
    FeasibleMarginals (canonicalMarginalConstraints k p) q ↔
      SameMarginalsUpTo k p q := by
  classical
  constructor
  · intro hFeasible scope hScope
    let constraint : MarginalConstraint Var :=
      { scope := scope
        target := marginal scope p }
    have hMem : constraint ∈ canonicalMarginalConstraints k p := by
      apply List.mem_map.mpr
      exact ⟨scope, (mem_scopesUpTo k scope).2 hScope, rfl⟩
    exact hFeasible constraint hMem
  · intro hSame constraint hConstraint
    rcases List.mem_map.mp hConstraint with ⟨scope, hScope, rfl⟩
    exact hSame scope ((mem_scopesUpTo k scope).1 hScope)

/-- **Lemma `lem:canonical`, marginal form.** A law is `k`-local exactly
when it maximizes entropy in the fiber of all its order-at-most-`k`
marginals. -/
theorem isKLocalMarginal_iff_maxEntropy_sameMarginals
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    IsKLocalMarginal k p ↔
      IsMaxEntropyAmong (SameMarginalsUpTo k p) p := by
  constructor
  · rintro ⟨constraints, hBound, hMax⟩
    refine ⟨sameMarginalsUpTo_refl k p, ?_⟩
    intro q hSame
    apply hMax.2 q
    intro constraint hConstraint
    calc
      marginal constraint.scope q = marginal constraint.scope p :=
        hSame constraint.scope (hBound constraint hConstraint)
      _ = constraint.target := hMax.1 constraint hConstraint
  · intro hMax
    refine ⟨canonicalMarginalConstraints k p,
      canonicalMarginalConstraints_respectK k p, ?_⟩
    constructor
    · exact (feasible_canonicalMarginalConstraints_iff k p p).2
        (sameMarginalsUpTo_refl k p)
    · intro q hFeasible
      exact hMax.2 q ((feasible_canonicalMarginalConstraints_iff k p q).1 hFeasible)

/-! ## Monomial features and Boolean Möbius inversion -/

/-- Coordinates on which a Boolean assignment is `true`. -/
def trueCoordinates
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (x : Assignment Var) : Finset Var :=
  Finset.univ.filter fun i => x i = true

@[simp]
theorem mem_trueCoordinates
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (x : Assignment Var) (i : Var) :
    i ∈ trueCoordinates x ↔ x i = true := by
  simp [trueCoordinates]

theorem trueCoordinates_injective
    {Var : Type u} [Fintype Var] [DecidableEq Var] :
    Function.Injective (trueCoordinates : Assignment Var → Finset Var) := by
  intro x y hxy
  funext i
  have hi := Finset.ext_iff.mp hxy i
  simp only [mem_trueCoordinates] at hi
  cases hxi : x i <;> cases hyi : y i <;> simp_all

/-- Assignments extending a prescribed set of true coordinates. -/
noncomputable def monomialExtensions
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (scope : Finset Var) : Finset (Assignment Var) :=
  Finset.univ.filter fun x => scope ⊆ trueCoordinates x

@[simp]
theorem mem_monomialExtensions
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (scope : Finset Var) (x : Assignment Var) :
    x ∈ monomialExtensions scope ↔ scope ⊆ trueCoordinates x := by
  classical
  simp [monomialExtensions]

/-- The real expectation of the Boolean monomial `y_scope`.  Since the
monomial is `1` exactly when every coordinate in `scope` is true, this is the
total mass of the corresponding upper event. -/
noncomputable def monomialMoment
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) (scope : Finset Var) : ℝ :=
  ∑ x ∈ monomialExtensions scope, (p x).toReal

/-- The real-valued Boolean monomial itself. -/
def monomialValue
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (scope : Finset Var) (x : Assignment Var) : ℝ :=
  if scope ⊆ trueCoordinates x then 1 else 0

theorem monomialMoment_eq_expectation
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) (scope : Finset Var) :
    monomialMoment p scope = pmfExpectation p (monomialValue scope) := by
  classical
  simp [monomialMoment, monomialExtensions, pmfExpectation, monomialValue,
    Finset.sum_filter]

/-- The order-`k` feature vector `χₖ`, indexed by subsets of cardinality at
most `k`.  Values are the real embeddings of the Boolean monomials. -/
abbrev FeatureScope
    (Var : Type u) [DecidableEq Var] (k : Nat) :=
  {scope : Finset Var // scope.card ≤ k}

def canonicalFeature
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (x : Assignment Var) :
    FeatureScope Var k → ℝ :=
  fun scope => monomialValue scope.1 x

/-- Equality of all order-at-most-`k` monomial moments. -/
def SameFeatureMomentsUpTo
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p q : Distribution (Assignment Var)) : Prop :=
  ∀ scope : Finset Var, scope.card ≤ k →
    monomialMoment q scope = monomialMoment p scope

theorem monomialMoment_trueCoordinates
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var)) (x : Assignment Var) :
    monomialMoment p (trueCoordinates x) =
        (p x).toReal +
          ∑ y ∈ (monomialExtensions (trueCoordinates x)).erase x, (p y).toReal := by
  classical
  have hx : x ∈ monomialExtensions (trueCoordinates x) := by simp
  rw [monomialMoment]
  have hErase := Finset.sum_erase_add
    (s := monomialExtensions (trueCoordinates x))
    (f := fun y => (p y).toReal) hx
  linarith

/-- Boolean Möbius inversion, in injectivity form: a law on a finite Boolean
cube is determined by all of its monomial moments. -/
theorem distribution_eq_of_monomialMoments_eq
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {p q : Distribution (Assignment Var)}
    (hMoments : ∀ scope : Finset Var,
      monomialMoment q scope = monomialMoment p scope) :
    q = p := by
  classical
  have hMassReal : ∀ n : Nat, ∀ x : Assignment Var,
      Fintype.card Var - (trueCoordinates x).card = n →
        (q x).toReal = (p x).toReal := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hxCount
        have hRest :
            (∑ y ∈ (monomialExtensions (trueCoordinates x)).erase x, (q y).toReal) =
              ∑ y ∈ (monomialExtensions (trueCoordinates x)).erase x, (p y).toReal := by
          apply Finset.sum_congr rfl
          intro y hy
          have hyMem : y ∈ monomialExtensions (trueCoordinates x) :=
            (Finset.mem_erase.mp hy).2
          have hyNe : y ≠ x := (Finset.mem_erase.mp hy).1
          have hSubset : trueCoordinates x ⊆ trueCoordinates y :=
            (mem_monomialExtensions (trueCoordinates x) y).1 hyMem
          have hStrict : trueCoordinates x ⊂ trueCoordinates y := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hSubset, ?_⟩
            intro hEq
            exact hyNe (trueCoordinates_injective hEq.symm)
          have hCardLt : (trueCoordinates x).card < (trueCoordinates y).card :=
            Finset.card_lt_card hStrict
          have hxCard : (trueCoordinates x).card ≤ Fintype.card Var :=
            Finset.card_le_univ _
          have hyCard : (trueCoordinates y).card ≤ Fintype.card Var :=
            Finset.card_le_univ _
          have hCountLt :
              Fintype.card Var - (trueCoordinates y).card < n := by
            omega
          exact ih _ hCountLt y rfl
        have hMoment := hMoments (trueCoordinates x)
        rw [monomialMoment_trueCoordinates q x,
          monomialMoment_trueCoordinates p x, hRest] at hMoment
        linarith
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff'
    (q.apply_ne_top x) (p.apply_ne_top x)).mp
  exact hMassReal _ x rfl

/-- Regard a finset of coordinates inside `scope` as a finset of ambient
coordinates. -/
def liftSubscope
    {Var : Type u} [DecidableEq Var]
    (scope : Finset Var) (subscope : Finset scope) : Finset Var :=
  subscope.map (Function.Embedding.subtype fun i : Var => i ∈ scope)

@[simp]
theorem mem_liftSubscope
    {Var : Type u} [DecidableEq Var]
    (scope : Finset Var) (subscope : Finset scope) (i : Var) :
    i ∈ liftSubscope scope subscope ↔ ∃ hi : i ∈ scope, (⟨i, hi⟩ : scope) ∈ subscope := by
  rw [liftSubscope, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.2, by simpa using hj⟩
  · rintro ⟨hi, hiSubscope⟩
    exact ⟨⟨i, hi⟩, hiSubscope, rfl⟩

@[simp]
theorem card_liftSubscope
    {Var : Type u} [DecidableEq Var]
    (scope : Finset Var) (subscope : Finset scope) :
    (liftSubscope scope subscope).card = subscope.card := by
  exact Finset.card_map _

theorem monomialValue_restrict
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (scope : Finset Var) (subscope : Finset scope) (x : Assignment Var) :
    monomialValue subscope (restrict scope x) =
      monomialValue (liftSubscope scope subscope) x := by
  classical
  unfold monomialValue
  apply if_congr
  · constructor
    · intro h i hi
      rcases (mem_liftSubscope scope subscope i).1 hi with ⟨hiScope, hiSubscope⟩
      apply (mem_trueCoordinates x i).2
      exact (mem_trueCoordinates (restrict scope x) ⟨i, hiScope⟩).1
        (h hiSubscope)
    · intro h i hi
      apply (mem_trueCoordinates (restrict scope x) i).2
      exact (mem_trueCoordinates x i.1).1
        (h ((mem_liftSubscope scope subscope i.1).2 ⟨i.2, hi⟩))
  · rfl
  · rfl

theorem monomialMoment_marginal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (p : Distribution (Assignment Var))
    (scope : Finset Var) (subscope : Finset scope) :
    monomialMoment (marginal scope p) subscope =
      monomialMoment p (liftSubscope scope subscope) := by
  rw [monomialMoment_eq_expectation, marginal, pmfExpectation_map,
    monomialMoment_eq_expectation]
  congr 1
  funext x
  exact monomialValue_restrict scope subscope x

@[simp]
theorem liftSubscope_univ
    {Var : Type u} [DecidableEq Var] (scope : Finset Var) :
    liftSubscope scope (Finset.univ : Finset scope) = scope := by
  ext i
  rw [mem_liftSubscope]
  constructor
  · rintro ⟨hi, _⟩
    exact hi
  · intro hi
    exact ⟨hi, Finset.mem_univ _⟩

@[simp]
theorem liftSubscope_attach
    {Var : Type u} [DecidableEq Var] (scope : Finset Var) :
    liftSubscope scope scope.attach = scope := by
  ext i
  rw [mem_liftSubscope]
  constructor
  · rintro ⟨hi, _⟩
    exact hi
  · intro hi
    refine ⟨hi, ?_⟩
    change (⟨i, hi⟩ : scope) ∈ (Finset.univ : Finset scope)
    exact Finset.mem_univ _

/-- Equality of all order-at-most-`k` monomial moments is equivalent to
equality of all order-at-most-`k` marginals. -/
theorem sameFeatureMomentsUpTo_iff_sameMarginalsUpTo
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p q : Distribution (Assignment Var)) :
    SameFeatureMomentsUpTo k p q ↔ SameMarginalsUpTo k p q := by
  classical
  constructor
  · intro hMoments scope hScope
    apply distribution_eq_of_monomialMoments_eq
    intro subscope
    rw [monomialMoment_marginal, monomialMoment_marginal]
    apply hMoments
    rw [card_liftSubscope]
    have hSubscope : subscope.card ≤ scope.card := by
      simpa using Finset.card_le_univ subscope
    exact Nat.le_trans hSubscope hScope
  · intro hMarginals scope hScope
    have hMarginal := hMarginals scope hScope
    have hMoment := congrArg
      (fun r : Distribution (Assignment scope) =>
        monomialMoment r (Finset.univ : Finset scope)) hMarginal
    simpa [monomialMoment_marginal] using hMoment

/-- **Lemma `lem:canonical`.** A distribution is `k`-local if and only if it
maximizes entropy among distributions with the same order-`k` monomial feature
moments `E[χₖ]`. -/
theorem isKLocalMarginal_iff_maxEntropy_sameFeatureMoments
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    IsKLocalMarginal k p ↔
      IsMaxEntropyAmong (SameFeatureMomentsUpTo k p) p := by
  constructor
  · intro hLocal
    have hMax := (isKLocalMarginal_iff_maxEntropy_sameMarginals k p).1 hLocal
    refine ⟨?_, ?_⟩
    · exact (sameFeatureMomentsUpTo_iff_sameMarginalsUpTo k p p).2 hMax.1
    · intro q hMoments
      exact hMax.2 q
        ((sameFeatureMomentsUpTo_iff_sameMarginalsUpTo k p q).1 hMoments)
  · intro hMax
    apply (isKLocalMarginal_iff_maxEntropy_sameMarginals k p).2
    refine ⟨?_, ?_⟩
    · exact (sameFeatureMomentsUpTo_iff_sameMarginalsUpTo k p p).1 hMax.1
    · intro q hMarginals
      exact hMax.2 q
        ((sameFeatureMomentsUpTo_iff_sameMarginalsUpTo k p q).2 hMarginals)

end KLocality
