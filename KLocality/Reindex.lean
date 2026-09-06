import KLocality.FaceGibbsCharacterization

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Reindexing finite Boolean models

All paper statements are invariant under bijective renaming of coordinates.
This file packages that fact at the assignment, feature-polynomial,
distribution, and locality levels.
-/

/-- Rename the coordinates of a Boolean assignment along an equivalence. -/
def assignmentEquiv
    {Var : Type u} {Var' : Type v} (equiv : Var ≃ Var') :
    Assignment Var ≃ Assignment Var' where
  toFun assignment coordinate := assignment (equiv.symm coordinate)
  invFun assignment coordinate := assignment (equiv coordinate)
  left_inv assignment := by
    funext coordinate
    simp
  right_inv assignment := by
    funext coordinate
    simp

@[simp]
theorem assignmentEquiv_apply
    {Var : Type u} {Var' : Type v} (equiv : Var ≃ Var')
    (assignment : Assignment Var) (coordinate : Var') :
    assignmentEquiv equiv assignment coordinate =
      assignment (equiv.symm coordinate) :=
  rfl

@[simp]
theorem assignmentEquiv_symm
    {Var : Type u} {Var' : Type v} (equiv : Var ≃ Var') :
    (assignmentEquiv equiv).symm = assignmentEquiv equiv.symm :=
  rfl

@[simp]
theorem assignmentEquiv_symm_apply_assignmentEquiv
    {Var : Type u} {Var' : Type v} (equiv : Var ≃ Var')
    (assignment : Assignment Var) :
    assignmentEquiv equiv.symm (assignmentEquiv equiv assignment) = assignment :=
  (assignmentEquiv equiv).symm_apply_apply assignment

@[simp]
theorem assignmentEquiv_apply_assignmentEquiv_symm
    {Var : Type u} {Var' : Type v} (equiv : Var ≃ Var')
    (assignment : Assignment Var') :
    assignmentEquiv equiv (assignmentEquiv equiv.symm assignment) = assignment :=
  (assignmentEquiv equiv).apply_symm_apply assignment

/-- Rename a feature scope without changing its cardinality bound. -/
def featureScopeEquiv
    {Var : Type u} {Var' : Type v}
    [DecidableEq Var] [DecidableEq Var']
    (equiv : Var ≃ Var') (k : Nat) :
    FeatureScope Var k ≃ FeatureScope Var' k where
  toFun scope :=
    ⟨equiv.finsetCongr scope.1, by
      simpa [Equiv.finsetCongr_apply] using scope.2⟩
  invFun scope :=
    ⟨equiv.symm.finsetCongr scope.1, by
      simpa [Equiv.finsetCongr_apply] using scope.2⟩
  left_inv scope := by
    apply Subtype.ext
    ext coordinate
    simp [Equiv.finsetCongr_apply]
  right_inv scope := by
    apply Subtype.ext
    ext coordinate
    simp [Equiv.finsetCongr_apply]

@[simp]
theorem featureScopeEquiv_val
    {Var : Type u} {Var' : Type v}
    [DecidableEq Var] [DecidableEq Var']
    (equiv : Var ≃ Var') (k : Nat) (scope : FeatureScope Var k) :
    (featureScopeEquiv equiv k scope).1 = equiv.finsetCongr scope.1 :=
  rfl

/-- Rename the variables of a canonical feature polynomial. -/
noncomputable def FeaturePolynomial.reindex
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    {k : Nat} (equiv : Var ≃ Var')
    (polynomial : FeaturePolynomial Var k) :
    FeaturePolynomial Var' k :=
  fun scope => polynomial ((featureScopeEquiv equiv k).symm scope)

theorem monomialValue_finsetCongr_assignmentEquiv
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    (equiv : Var ≃ Var') (scope : Finset Var) (x : Assignment Var) :
    monomialValue (equiv.finsetCongr scope) (assignmentEquiv equiv x) =
      monomialValue scope x := by
  classical
  have hSubset :
      equiv.finsetCongr scope ⊆ trueCoordinates (assignmentEquiv equiv x) ↔
        scope ⊆ trueCoordinates x := by
    constructor
    · intro h i hi
      have hei : equiv i ∈ equiv.finsetCongr scope := by
        simp [Equiv.finsetCongr_apply, hi]
      have hTrue := h hei
      rw [mem_trueCoordinates] at hTrue ⊢
      simpa using hTrue
    · intro h j hj
      rw [Equiv.finsetCongr_apply] at hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      subst j
      rw [mem_trueCoordinates]
      simpa using (show x i = true from (mem_trueCoordinates x i).1 (h hi))
  by_cases h : scope ⊆ trueCoordinates x
  · have hMapped : equiv.finsetCongr scope ⊆
        trueCoordinates (assignmentEquiv equiv x) := hSubset.2 h
    have hMapped' : Finset.map equiv.toEmbedding scope ⊆
        trueCoordinates (assignmentEquiv equiv x) := by
      simpa [Equiv.finsetCongr_apply] using hMapped
    simp [monomialValue, h, hMapped']
  · have hMapped : ¬equiv.finsetCongr scope ⊆
        trueCoordinates (assignmentEquiv equiv x) := by
      intro hContra
      exact h (hSubset.1 hContra)
    have hMapped' : ¬Finset.map equiv.toEmbedding scope ⊆
        trueCoordinates (assignmentEquiv equiv x) := by
      simpa [Equiv.finsetCongr_apply] using hMapped
    simp [monomialValue, h, hMapped']

@[simp]
theorem FeaturePolynomial.eval_reindex_assignmentEquiv
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    {k : Nat} (equiv : Var ≃ Var')
    (polynomial : FeaturePolynomial Var k) (x : Assignment Var) :
    (polynomial.reindex equiv).eval (assignmentEquiv equiv x) =
      polynomial.eval x := by
  classical
  let scopeEquiv := featureScopeEquiv equiv k
  unfold FeaturePolynomial.eval FeaturePolynomial.reindex
  rw [← scopeEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro scope _
  dsimp only [scopeEquiv]
  rw [Equiv.symm_apply_apply]
  change polynomial scope *
      monomialValue (equiv.finsetCongr scope.1) (assignmentEquiv equiv x) =
    polynomial scope * monomialValue scope.1 x
  rw [monomialValue_finsetCongr_assignmentEquiv]

/-- Push a finite PMF forward along coordinate renaming. -/
noncomputable def reindexDistribution
    {Var : Type u} {Var' : Type v}
    (equiv : Var ≃ Var')
    (p : Distribution (Assignment Var)) :
    Distribution (Assignment Var') :=
  p.map (assignmentEquiv equiv)

@[simp]
theorem map_equiv_apply
    {α : Type u} {β : Type v}
    (p : Distribution α) (equiv : α ≃ β) (y : β) :
    p.map equiv y = p (equiv.symm y) := by
  rw [PMF.map_apply]
  rw [tsum_eq_single (equiv.symm y)]
  · simp
  · intro x hx
    have hNe : y ≠ equiv x := by
      intro hEq
      apply hx
      exact equiv.injective (by simpa using hEq.symm)
    simp [hNe]

@[simp]
theorem reindexDistribution_apply_assignmentEquiv
    {Var : Type u} {Var' : Type v}
    (equiv : Var ≃ Var')
    (p : Distribution (Assignment Var)) (x : Assignment Var) :
    reindexDistribution equiv p (assignmentEquiv equiv x) = p x := by
  rw [reindexDistribution, map_equiv_apply]
  simp

theorem mem_support_reindexDistribution_iff
    {Var : Type u} {Var' : Type v}
    (equiv : Var ≃ Var')
    (p : Distribution (Assignment Var)) (y : Assignment Var') :
    y ∈ (reindexDistribution equiv p).support ↔
      assignmentEquiv equiv.symm y ∈ p.support := by
  rw [reindexDistribution, PMF.support_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨assignmentEquiv equiv.symm y, hy, by simp⟩

@[simp]
theorem reindexDistribution_symm_reindexDistribution
    {Var : Type u} {Var' : Type v}
    (equiv : Var ≃ Var')
    (p : Distribution (Assignment Var)) :
    reindexDistribution equiv.symm (reindexDistribution equiv p) = p := by
  unfold reindexDistribution
  rw [PMF.map_comp]
  rw [show assignmentEquiv equiv.symm ∘ assignmentEquiv equiv = id by
    funext x
    simp]
  exact PMF.map_id p

@[simp]
theorem reindexDistribution_reindexDistribution_symm
    {Var : Type u} {Var' : Type v}
    (equiv : Var ≃ Var')
    (p : Distribution (Assignment Var')) :
    reindexDistribution equiv (reindexDistribution equiv.symm p) = p := by
  simpa using reindexDistribution_symm_reindexDistribution equiv.symm p

/-- Face--Gibbs certificates transport under a bijective coordinate rename. -/
theorem isFaceGibbs_reindexDistribution
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    (equiv : Var ≃ Var') (k : Nat)
    (p : Distribution (Assignment Var))
    (hFaceGibbs : IsFaceGibbs k p) :
    IsFaceGibbs k (reindexDistribution equiv p) := by
  classical
  rcases hFaceGibbs with ⟨⟨energy, hNonneg, hZero⟩, theta, hLog⟩
  refine ⟨⟨energy.reindex equiv, ?_, ?_⟩, theta.reindex equiv, ?_⟩
  · intro y
    rcases (assignmentEquiv equiv).surjective y with ⟨x, rfl⟩
    simpa using hNonneg x
  · intro y
    rcases (assignmentEquiv equiv).surjective y with ⟨x, rfl⟩
    rw [FeaturePolynomial.eval_reindex_assignmentEquiv]
    exact (hZero x).trans (by
      rw [mem_support_reindexDistribution_iff]
      simp)
  · intro y hySupport
    rcases (assignmentEquiv equiv).surjective y with ⟨x, rfl⟩
    have hxSupport : x ∈ p.support := by
      simpa using
        (mem_support_reindexDistribution_iff equiv p
          (assignmentEquiv equiv x)).1 hySupport
    simp [hLog x hxSupport]

/-- `k`-locality is invariant under bijective renaming of Boolean
coordinates. -/
theorem isKLocalMarginal_reindexDistribution_iff
    {Var : Type u} {Var' : Type v}
    [Fintype Var] [Fintype Var'] [DecidableEq Var] [DecidableEq Var']
    (equiv : Var ≃ Var') (k : Nat)
    (p : Distribution (Assignment Var)) :
    IsKLocalMarginal k (reindexDistribution equiv p) ↔
      IsKLocalMarginal k p := by
  constructor
  · intro hRenamed
    have hBack := isFaceGibbs_reindexDistribution equiv.symm k
      (reindexDistribution equiv p)
      ((isKLocalMarginal_iff_isFaceGibbs k _).1 hRenamed)
    rw [reindexDistribution_symm_reindexDistribution] at hBack
    exact isKLocalMarginal_of_isFaceGibbs k p hBack
  · intro hLocal
    exact isKLocalMarginal_of_isFaceGibbs k _
      (isFaceGibbs_reindexDistribution equiv k p
        ((isKLocalMarginal_iff_isFaceGibbs k p).1 hLocal))

/-- Transport both visible and hidden coordinate types without changing their roles. -/
noncomputable def KLocalization.reindex
    {k : Nat} {V H V' H' : Type*}
    [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [Fintype V'] [DecidableEq V'] [Fintype H'] [DecidableEq H']
    {p : Distribution (Assignment V)} (loc : KLocalization k V H p)
    (ev : V ≃ V') (eh : H ≃ H') :
    KLocalization k V' H' (reindexDistribution ev p) where
  lifted := reindexDistribution (Equiv.sumCongr ev eh) loc.lifted
  marginal := by
    unfold IsMarginalModel reindexDistribution
    rw [PMF.map_comp]
    have h := congrArg (fun q => q.map (assignmentEquiv ev)) loc.marginal
    dsimp only at h
    rw [PMF.map_comp] at h
    exact h
  kLocal := (isKLocalMarginal_reindexDistribution_iff _ _ _).mpr loc.kLocal

end KLocality
