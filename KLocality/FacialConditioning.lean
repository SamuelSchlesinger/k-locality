import KLocality.NoLatent
import KLocality.FeatureEmbedding

namespace KLocality

open scoped BigOperators

universe u v

/-!
# Conditioning on a facial event

Filtering a local law by the zero set of another nonnegative degree-`k`
polynomial intersects two exposed supports.  The original log-density is
unchanged up to the normalization constant, absorbed by the constant feature.
-/

/-- A set has positive mass under `p` exactly when we can exhibit a point in
both the set and the PMF support.  This is the witness format expected by
`PMF.filter`. -/
abbrev HasPositiveSupportIntersection
    {α : Type u} (p : Distribution α) (event : Set α) : Prop :=
  ∃ x ∈ event, x ∈ p.support

/-- Filtering by a preimage commutes with pushing a finite PMF forward. -/
theorem map_filter_preimage
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p : Distribution α) (map : α → β) (event : Set β)
    (hPositive : ∃ y ∈ event, y ∈ (p.map map).support)
    (hPositivePreimage : ∃ x ∈ map ⁻¹' event, x ∈ p.support) :
    (p.filter (map ⁻¹' event) hPositivePreimage).map map =
      (p.map map).filter event hPositive := by
  classical
  have hNormalizer :
      (∑' x, (map ⁻¹' event).indicator p x) =
        ∑' y, event.indicator (p.map map) y := by
    simp only [tsum_fintype, Set.indicator_apply, Set.mem_preimage, PMF.map_apply]
    calc
      (∑ x, if map x ∈ event then p x else 0) =
          ∑ x, ∑ y,
            if y ∈ event then (if y = map x then p x else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Fintype.sum_eq_single (map x)]
        · simp
        · intro y hy
          simp [hy]
      _ = ∑ y, ∑ x,
          if y ∈ event then (if y = map x then p x else 0) else 0 :=
        Finset.sum_comm
      _ = ∑ y,
          if y ∈ event then ∑ x, if y = map x then p x else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ event <;> simp [hy]
  apply PMF.ext
  intro y
  rw [PMF.map_apply, PMF.filter_apply]
  simp only [tsum_fintype]
  simp_rw [PMF.filter_apply]
  simp only [tsum_fintype]
  have hFactor :
      (∑ x, if y = map x then
          (map ⁻¹' event).indicator p x *
            (∑ x', (map ⁻¹' event).indicator p x')⁻¹ else 0) =
        (∑ x, if y = map x then
            (map ⁻¹' event).indicator p x else 0) *
          (∑ x', (map ⁻¹' event).indicator p x')⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hyx : y = map x <;> simp [hyx]
  rw [hFactor]
  have hNormalizerFin :
      (∑ x, (map ⁻¹' event).indicator p x) =
        ∑ y, event.indicator (p.map map) y := by
    simpa only [tsum_fintype] using hNormalizer
  rw [hNormalizerFin]
  have hNumerator :
      (∑ x, if y = map x then
          (map ⁻¹' event).indicator p x else 0) =
        event.indicator (p.map map) y := by
    by_cases hy : y ∈ event
    · rw [Set.indicator_of_mem hy, PMF.map_apply]
      simp only [tsum_fintype]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hyx : y = map x
      · subst y
        simp [hy]
      · simp [hyx]
    · rw [Set.indicator_of_notMem hy]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hyx : y = map x
      · subst y
        simp [hy]
      · simp [hyx]
  rw [hNumerator]

/-- Filtering a face--Gibbs law by another degree-`k` facial event preserves
the face--Gibbs property. -/
theorem isFaceGibbs_filter_of_isFacialSupport
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (p : Distribution (Assignment Var))
    (event : Set (Assignment Var))
    (hPositive : HasPositiveSupportIntersection p event)
    (hEventFacial : IsFacialSupport k event)
    (hFaceGibbs : IsFaceGibbs k p) :
    IsFaceGibbs k (p.filter event hPositive) := by
  classical
  rcases hFaceGibbs with ⟨⟨supportEnergy, hSupportNonneg, hSupportZero⟩,
    theta, hLog⟩
  rcases hEventFacial with ⟨eventEnergy, hEventNonneg, hEventZero⟩
  let combinedEnergy : FeaturePolynomial Var k := supportEnergy + eventEnergy
  have hCombinedNonneg : ∀ x, 0 ≤ combinedEnergy.eval x := by
    intro x
    simp only [combinedEnergy, FeaturePolynomial.eval_add]
    exact add_nonneg (hSupportNonneg x) (hEventNonneg x)
  have hCombinedZero : ∀ x,
      combinedEnergy.eval x = 0 ↔ x ∈ (p.filter event hPositive).support := by
    intro x
    rw [PMF.mem_support_filter_iff]
    simp only [combinedEnergy, FeaturePolynomial.eval_add]
    constructor
    · intro hSumZero
      have hSupportEnergyZero : supportEnergy.eval x = 0 := by
        nlinarith [hSupportNonneg x, hEventNonneg x]
      have hEventEnergyZero : eventEnergy.eval x = 0 := by
        nlinarith [hSupportNonneg x, hEventNonneg x]
      exact ⟨(hEventZero x).1 hEventEnergyZero,
        (hSupportZero x).1 hSupportEnergyZero⟩
    · rintro ⟨hxEvent, hxSupport⟩
      rw [(hSupportZero x).2 hxSupport, (hEventZero x).2 hxEvent, add_zero]
  let normalizer : ENNReal := ∑' x, event.indicator p x
  have hNormalizerNeZero : normalizer ≠ 0 := by
    simpa [normalizer] using hPositive
  have hNormalizerNeTop : normalizer ≠ ⊤ := by
    simpa [normalizer] using p.tsum_coe_indicator_ne_top event
  have hNormalizerRealPos : 0 < normalizer.toReal :=
    ENNReal.toReal_pos hNormalizerNeZero hNormalizerNeTop
  let adjustedTheta : FeaturePolynomial Var k :=
    theta - FeaturePolynomial.constant k (Real.log normalizer.toReal)
  have hAdjustedLog : ∀ x ∈ (p.filter event hPositive).support,
      Real.log ((p.filter event hPositive x).toReal) = adjustedTheta.eval x := by
    intro x hxFiltered
    have hxBoth := (PMF.mem_support_filter_iff hPositive).1 hxFiltered
    have hpPos : 0 < (p x).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff p x).1 hxBoth.2) (p.apply_ne_top x)
    rw [PMF.filter_apply]
    have hIndicator : event.indicator p x = p x := Set.indicator_of_mem hxBoth.1 _
    rw [hIndicator, ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hNormalizerRealNeZero : normalizer.toReal ≠ 0 := hNormalizerRealPos.ne'
    rw [Real.log_mul hpPos.ne' (inv_ne_zero hNormalizerRealNeZero),
      Real.log_inv, hLog x hxBoth.2]
    have hAdjustedEval : adjustedTheta.eval x =
        theta.eval x - Real.log normalizer.toReal := by
      dsimp only [adjustedTheta]
      rw [FeaturePolynomial.eval_sub, FeaturePolynomial.eval_constant]
    rw [hAdjustedEval]
    ring
  exact ⟨⟨combinedEnergy, hCombinedNonneg, hCombinedZero⟩,
    adjustedTheta, hAdjustedLog⟩

/-- Conditioning a `k`-local law on a degree-`k` facial event preserves
`k`-locality. -/
theorem isKLocalMarginal_filter_of_isFacialSupport
    {Var : Type u} [Fintype Var] [DecidableEq Var]
    {k : Nat} (p : Distribution (Assignment Var))
    (event : Set (Assignment Var))
    (hPositive : HasPositiveSupportIntersection p event)
    (hEventFacial : IsFacialSupport k event)
    (hLocal : IsKLocalMarginal k p) :
    IsKLocalMarginal k (p.filter event hPositive) :=
  isKLocalMarginal_of_isFaceGibbs k _
    (isFaceGibbs_filter_of_isFacialSupport p event hPositive hEventFacial
      ((isKLocalMarginal_iff_isFaceGibbs k p).1 hLocal))

/-- Condition a localization on an event depending only on its observed
coordinates. -/
def liftedEvent
    {ObsVar : Type u} {LatVar : Type v}
    (event : Set (Assignment ObsVar)) :
    Set (Assignment (Sum ObsVar LatVar)) :=
  projectObs ⁻¹' event

/-- The polynomial exposing an observed event lifts to the joint cube without
increasing degree. -/
noncomputable def FeaturePolynomial.liftObserved
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [Fintype LatVar]
    [DecidableEq ObsVar] [DecidableEq LatVar]
    {k : Nat} (polynomial : FeaturePolynomial ObsVar k) :
    FeaturePolynomial (Sum ObsVar LatVar) k :=
  polynomial.extendAlong ⟨Sum.inl, Sum.inl_injective⟩

@[simp]
theorem FeaturePolynomial.eval_liftObserved
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [Fintype LatVar]
    [DecidableEq ObsVar] [DecidableEq LatVar]
    {k : Nat} (polynomial : FeaturePolynomial ObsVar k)
    (assignment : Assignment (Sum ObsVar LatVar)) :
    polynomial.liftObserved.eval assignment =
      polynomial.eval (projectObs assignment) := by
  exact FeaturePolynomial.eval_extendAlong _ polynomial assignment

/-- The preimage of a facial observed event is facial on the joint cube. -/
theorem isFacialSupport_liftedEvent
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [Fintype LatVar]
    [DecidableEq ObsVar] [DecidableEq LatVar]
    {k : Nat} {event : Set (Assignment ObsVar)}
    (hFacial : IsFacialSupport k event) :
    IsFacialSupport k (liftedEvent (LatVar := LatVar) event) := by
  rcases hFacial with ⟨energy, hNonneg, hZero⟩
  refine ⟨energy.liftObserved, ?_, ?_⟩
  · intro assignment
    rw [FeaturePolynomial.eval_liftObserved]
    exact hNonneg _
  · intro assignment
    rw [FeaturePolynomial.eval_liftObserved, hZero]
    rfl

/-- An observed positive event has positive preimage in every joint marginal
model. -/
theorem exists_support_lift_of_isMarginalModel
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [Fintype LatVar]
    (pObs : Distribution (Assignment ObsVar))
    (pJoint : Distribution (Assignment (Sum ObsVar LatVar)))
    (hMarginal : IsMarginalModel pObs pJoint)
    (event : Set (Assignment ObsVar))
    (hPositive : HasPositiveSupportIntersection pObs event) :
    HasPositiveSupportIntersection pJoint
      (liftedEvent (LatVar := LatVar) event) := by
  rcases hPositive with ⟨x, hxEvent, hxSupport⟩
  have hxMapped : x ∈ (pJoint.map projectObs).support := by
    rw [hMarginal]
    exact hxSupport
  rcases (PMF.mem_support_map_iff projectObs pJoint x).1 hxMapped with
    ⟨joint, hJointSupport, hProject⟩
  refine ⟨joint, ?_, hJointSupport⟩
  change projectObs joint ∈ event
  rwa [hProject]

/-- Conditioning a concrete localization on a facial observed event preserves
the latent-variable type and localizes the conditional observed law. -/
noncomputable def KLocalization.filterFacial
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [Fintype LatVar]
    [DecidableEq ObsVar] [DecidableEq LatVar]
    {k : Nat} {pObs : Distribution (Assignment ObsVar)}
    (localization : KLocalization k ObsVar LatVar pObs)
    (event : Set (Assignment ObsVar))
    (hPositive : HasPositiveSupportIntersection pObs event)
    (hFacial : IsFacialSupport k event) :
    KLocalization k ObsVar LatVar (pObs.filter event hPositive) := by
  classical
  let jointEvent := liftedEvent (LatVar := LatVar) event
  have hJointPositive : HasPositiveSupportIntersection localization.lifted jointEvent :=
    exists_support_lift_of_isMarginalModel pObs localization.lifted
      localization.marginal event hPositive
  let filteredJoint := localization.lifted.filter jointEvent hJointPositive
  refine {
    lifted := filteredJoint
    marginal := ?_
    kLocal := ?_ }
  · dsimp only [filteredJoint, jointEvent, liftedEvent]
    have hMappedPositive : HasPositiveSupportIntersection
        (localization.lifted.map projectObs) event := by
      rw [localization.marginal]
      exact hPositive
    have hCommute := map_filter_preimage localization.lifted projectObs event
      hMappedPositive hJointPositive
    have hFilterEq :
        (localization.lifted.map projectObs).filter event hMappedPositive =
          pObs.filter event hPositive := by
      have hMarginalEq : localization.lifted.map projectObs = pObs :=
        localization.marginal
      apply PMF.ext
      intro x
      rw [PMF.filter_apply, PMF.filter_apply]
      have hPoint : localization.lifted.map projectObs x = pObs x :=
        congrArg (fun q : Distribution (Assignment ObsVar) => q x) hMarginalEq
      have hIndicatorPoint :
          event.indicator (localization.lifted.map projectObs) x =
            event.indicator pObs x := by
        by_cases hx : x ∈ event <;> simp [hx, hPoint]
      have hNormalizer :
          (∑' y, event.indicator (localization.lifted.map projectObs) y) =
            ∑' y, event.indicator pObs y := by
        exact congrArg
          (fun q : Distribution (Assignment ObsVar) =>
            ∑' y, event.indicator q y) hMarginalEq
      rw [hIndicatorPoint, hNormalizer]
    exact hCommute.trans hFilterEq
  · exact isKLocalMarginal_filter_of_isFacialSupport localization.lifted jointEvent
      hJointPositive (isFacialSupport_liftedEvent (LatVar := LatVar) hFacial)
      localization.kLocal

/-- **Lemma `lem:facial-conditioning`, first assertion.** Conditioning on a
positive degree-`k` facial event cannot increase localization complexity. -/
theorem localizationComplexity_filter_le
    {ObsVar : Type u} [Fintype ObsVar] [DecidableEq ObsVar]
    {k : Nat} (hk : 2 ≤ k)
    (p : Distribution (Assignment ObsVar))
    (event : Set (Assignment ObsVar))
    (hPositive : HasPositiveSupportIntersection p event)
    (hFacial : IsFacialSupport k event) :
    localizationComplexity k ObsVar (p.filter event hPositive) ≤
      localizationComplexity k ObsVar p := by
  let latentVars := localizationComplexity k ObsVar p
  rcases localizationComplexity_spec k ObsVar p (kLocalization_exists p hk) with
    ⟨localization⟩
  apply localizationComplexity_min
  exact ⟨localization.filterFacial event hPositive hFacial⟩

end KLocality
