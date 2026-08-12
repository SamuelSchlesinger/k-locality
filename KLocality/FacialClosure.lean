import KLocality.FacialSupport

namespace KLocality

universe u

/-!
# Facial closure as a moment-fiber support

For a finite Boolean law `p`, the smallest degree-`k` facial support containing
`p.support` is exactly the union of the supports of all laws having the same
order-at-most-`k` moments as `p`.  This is the computational form of the
relative-interior statement used by the selector lower-bound method.
-/

@[refl]
theorem sameFeatureMomentsUpTo_refl
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    SameFeatureMomentsUpTo k p p := by
  intro scope _
  rfl

@[symm]
theorem SameFeatureMomentsUpTo.symm
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p q : Distribution (Assignment Var)}
    (h : SameFeatureMomentsUpTo k p q) :
    SameFeatureMomentsUpTo k q p := by
  intro scope hScope
  exact (h scope hScope).symm

@[trans]
theorem SameFeatureMomentsUpTo.trans
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p q r : Distribution (Assignment Var)}
    (hpq : SameFeatureMomentsUpTo k p q)
    (hqr : SameFeatureMomentsUpTo k q r) :
    SameFeatureMomentsUpTo k p r := by
  intro scope hScope
  exact (hqr scope hScope).trans (hpq scope hScope)

/-- The union of the supports in the order-`k` moment fiber of `p`. -/
def momentFacialClosure
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) : Set (Assignment Var) :=
  {x | ∃ q : Distribution (Assignment Var),
    SameFeatureMomentsUpTo k p q ∧ x ∈ q.support}

@[simp]
theorem mem_momentFacialClosure_iff
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p : Distribution (Assignment Var)}
    {x : Assignment Var} :
    x ∈ momentFacialClosure k p ↔
      ∃ q : Distribution (Assignment Var),
        SameFeatureMomentsUpTo k p q ∧ x ∈ q.support :=
  Iff.rfl

theorem support_subset_momentFacialClosure
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    p.support ⊆ momentFacialClosure k p := by
  intro x hx
  exact ⟨p, sameFeatureMomentsUpTo_refl k p, hx⟩

/-- If a facial target contains the reference support, every law in the same
moment fiber is supported in that target. -/
theorem support_subset_facialTarget_of_sameFeatureMoments
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p q : Distribution (Assignment Var)}
    {target : Set (Assignment Var)}
    (hFacial : IsFacialSupport k target)
    (hpSupport : p.support ⊆ target)
    (hMoments : SameFeatureMomentsUpTo k p q) :
    q.support ⊆ target := by
  rcases hFacial with ⟨energy, hNonneg, hZero⟩
  have hpZero : p.support ⊆ {x | energy.eval x = 0} := by
    intro x hx
    exact (hZero x).2 (hpSupport hx)
  have hpExpectation : pmfExpectation p energy.eval = 0 :=
    pmfExpectation_eq_zero_of_support_subset_zeroSet p energy.eval hpZero
  have hqExpectation : pmfExpectation q energy.eval = 0 := by
    rw [energy.expectation_eval_eq_of_sameFeatureMoments hMoments]
    exact hpExpectation
  have hqZero := support_subset_zeroSet_of_pmfExpectation_eq_zero
    q energy.eval hNonneg hqExpectation
  intro x hx
  exact (hZero x).1 (hqZero hx)

/-- A finite moment fiber has a single member whose support is the union of
all supports in the fiber.  It is obtained by uniformly mixing one witness
for every reachable cube point. -/
theorem exists_distribution_support_eq_momentFacialClosure
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    ∃ q : Distribution (Assignment Var),
      SameFeatureMomentsUpTo k p q ∧
        q.support = momentFacialClosure k p := by
  classical
  have hChoice : ∀ y : Assignment Var,
      ∃ q : Distribution (Assignment Var),
        SameFeatureMomentsUpTo k p q ∧
          (y ∈ momentFacialClosure k p → y ∈ q.support) := by
    intro y
    by_cases hy : y ∈ momentFacialClosure k p
    · rcases hy with ⟨q, hMoments, hySupport⟩
      exact ⟨q, hMoments, fun _ => hySupport⟩
    · exact ⟨p, sameFeatureMomentsUpTo_refl k p, fun hy' => (hy hy').elim⟩
  let family : Assignment Var → Distribution (Assignment Var) :=
    fun y => Classical.choose (hChoice y)
  have hFamilyMoments (y : Assignment Var) :
      SameFeatureMomentsUpTo k p (family y) :=
    (Classical.choose_spec (hChoice y)).1
  have hFamilyOwn (y : Assignment Var)
      (hy : y ∈ momentFacialClosure k p) : y ∈ (family y).support :=
    (Classical.choose_spec (hChoice y)).2 hy
  let average : Distribution (Assignment Var) :=
    (PMF.uniformOfFintype (Assignment Var)).bind family
  have hAverageMoments : SameFeatureMomentsUpTo k p average := by
    apply (sameFeatureMomentsUpTo_iff_sameMarginalsUpTo k p average).2
    intro scope hScope
    have hFamilyMarginal (y : Assignment Var) :
        marginal scope (family y) = marginal scope p :=
      ((sameFeatureMomentsUpTo_iff_sameMarginalsUpTo k p (family y)).1
        (hFamilyMoments y)) scope hScope
    unfold marginal
    change ((PMF.uniformOfFintype (Assignment Var)).bind family).map
        (restrict scope) = p.map (restrict scope)
    calc
      _ = (PMF.uniformOfFintype (Assignment Var)).bind
          (fun y => (family y).map (restrict scope)) :=
        PMF.map_bind _ _ _
      _ = (PMF.uniformOfFintype (Assignment Var)).bind
          (fun _ => p.map (restrict scope)) := by
        congr 1
        funext y
        exact hFamilyMarginal y
      _ = p.map (restrict scope) := PMF.bind_const _ _
  have hAverageSupport : average.support = momentFacialClosure k p := by
    ext x
    constructor
    · intro hx
      rcases (PMF.mem_support_bind_iff
          (PMF.uniformOfFintype (Assignment Var)) family x).1 hx with
        ⟨y, _hyUniform, hxFamily⟩
      exact ⟨family y, hFamilyMoments y, hxFamily⟩
    · intro hx
      apply (PMF.mem_support_bind_iff
        (PMF.uniformOfFintype (Assignment Var)) family x).2
      exact ⟨x, PMF.mem_support_uniformOfFintype x, hFamilyOwn x hx⟩
  exact ⟨average, hAverageMoments, hAverageSupport⟩

/-- The moment-fiber union is a degree-`k` facial support. -/
theorem momentFacialClosure_isFacial
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    (k : Nat) (p : Distribution (Assignment Var)) :
    IsFacialSupport k (momentFacialClosure k p) := by
  rcases exists_distribution_support_eq_momentFacialClosure k p with
    ⟨maximal, hMoments, hSupport⟩
  rw [← hSupport]
  apply isFacialSupport_of_maximal_momentFiber_support k maximal
  intro q hqMoments x hx
  rw [hSupport]
  exact ⟨q, hMoments.trans hqMoments, hx⟩

/-- The moment-fiber union is the smallest degree-`k` facial support
containing the support of `p`. -/
theorem momentFacialClosure_minimal
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} {p : Distribution (Assignment Var)}
    {target : Set (Assignment Var)}
    (hFacial : IsFacialSupport k target)
    (hContains : p.support ⊆ target) :
    momentFacialClosure k p ⊆ target := by
  intro x hx
  rcases hx with ⟨q, hMoments, hxSupport⟩
  exact support_subset_facialTarget_of_sameFeatureMoments
    hFacial hContains hMoments hxSupport

end KLocality
