import KLocality.GroundState

namespace KLocality

universe u v

/-!
# Uniform ground-state projections

This module records the finite counting fact used by circuit and verifier lifts: if projection
is a bijection from a nonempty lifted set onto a nonempty visible set, then projecting the
uniform law on the lifted set gives the uniform law on the visible set.
-/

/-- A bijection between two finite supports carries the uniform PMF on the source to the
uniform PMF on the target. -/
theorem map_uniformOn_eq_uniformOn_of_bijOn
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (source : Finset α) (hSource : source.Nonempty)
    (target : Finset β) (hTarget : target.Nonempty)
    (project : α → β)
    (hBij : Set.BijOn project (source : Set α) (target : Set β)) :
    (uniformOn source hSource).map project = uniformOn target hTarget := by
  apply PMF.ext
  intro y
  rw [PMF.map_apply]
  by_cases hy : y ∈ target
  · rcases hBij.surjOn hy with ⟨x, hxSource, hxProject⟩
    have hCard : source.card = target.card :=
      hBij.finsetCard_eq project
    rw [uniformOn_apply_of_mem hTarget hy]
    rw [tsum_eq_single x]
    · simp [hxProject, uniformOn_apply_of_mem hSource hxSource, hCard]
    · intro z hz
      by_cases hzSource : z ∈ source
      · have hyz : y ≠ project z := by
          intro hEquals
          apply hz
          apply hBij.injOn hzSource hxSource
          exact hEquals.symm.trans hxProject.symm
        simp [hyz]
      · simp [uniformOn_apply_of_notMem hSource hzSource]
  · rw [uniformOn_apply_of_notMem hTarget hy]
    rw [← tsum_zero]
    apply tsum_congr
    intro x
    by_cases hxSource : x ∈ source
    · have hyProject : y ≠ project x := by
        intro hEquals
        apply hy
        rw [hEquals]
        exact hBij.mapsTo hxSource
      simp [hyProject]
    · simp [uniformOn_apply_of_notMem hSource hxSource]

/-- Explicit unique-extension form of `map_uniformOn_eq_uniformOn_of_bijOn`.

Every source point must project into `target`, and every target point must have exactly one
preimage in `source`. -/
theorem map_uniformOn_eq_uniformOn_of_unique_extension
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (source : Finset α) (hSource : source.Nonempty)
    (target : Finset β) (hTarget : target.Nonempty)
    (project : α → β)
    (hMapsTo : ∀ x ∈ source, project x ∈ target)
    (hUnique : ∀ y ∈ target, ∃! x, x ∈ source ∧ project x = y) :
    (uniformOn source hSource).map project = uniformOn target hTarget := by
  apply map_uniformOn_eq_uniformOn_of_bijOn source hSource target hTarget project
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hMapsTo x hx
  · intro x hxSource z hzSource hProject
    have hy : project x ∈ target := hMapsTo x hxSource
    rcases hUnique (project x) hy with ⟨w, hw, hOnly⟩
    have hxw : x = w := hOnly x ⟨hxSource, rfl⟩
    have hzw : z = w := hOnly z ⟨hzSource, hProject.symm⟩
    exact hxw.trans hzw.symm
  · intro y hy
    rcases hUnique y hy with ⟨x, hx, _hOnly⟩
    exact ⟨x, hx.1, hx.2⟩

/-- A unique lifted extension of every visible state makes the uniform lifted law a marginal
model of the uniform visible law. -/
theorem uniformOn_isMarginalModel_of_unique_extension
    {ObsVar : Type u} {LatVar : Type v}
    [Fintype ObsVar] [DecidableEq ObsVar]
    [Fintype LatVar] [DecidableEq LatVar]
    (liftedSet : Finset (Assignment (Sum ObsVar LatVar)))
    (hLifted : liftedSet.Nonempty)
    (visibleSet : Finset (Assignment ObsVar))
    (hVisible : visibleSet.Nonempty)
    (hMapsTo : ∀ z ∈ liftedSet, projectObs z ∈ visibleSet)
    (hUnique : ∀ x ∈ visibleSet,
      ∃! z, z ∈ liftedSet ∧ projectObs z = x) :
    IsMarginalModel (uniformOn visibleSet hVisible) (uniformOn liftedSet hLifted) := by
  exact map_uniformOn_eq_uniformOn_of_unique_extension
    liftedSet hLifted visibleSet hVisible projectObs hMapsTo hUnique

end KLocality
