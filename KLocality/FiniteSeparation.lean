import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace KLocality

open Set

universe u

/-!
# Finite strict separation

The lemma below is a finite-dimensional form of Stiemke's alternative.  It is
the strict-complementarity engine used to expose maximal supports of moment
fibers.
-/

/-- If a linear subspace misses the standard simplex, there is a linear
functional vanishing on the subspace and strictly positive on every standard
basis vector. -/
theorem exists_strictlyPositive_annihilator
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (subspace : Submodule ℝ (ι → ℝ))
    (hDisjoint : Disjoint (subspace : Set (ι → ℝ)) (stdSimplex ℝ ι)) :
    ∃ functional : (ι → ℝ) →ₗ[ℝ] ℝ,
      (∀ vector ∈ subspace, functional vector = 0) ∧
        ∀ i, 0 < functional (Pi.single i 1) := by
  have hSubspaceClosed : IsClosed (subspace : Set (ι → ℝ)) :=
    Submodule.closed_of_finiteDimensional subspace
  obtain ⟨functional, lower, upper, hSubspace, hGap, hSimplex⟩ :=
    geometric_hahn_banach_closed_compact subspace.convex hSubspaceClosed
      (convex_stdSimplex ℝ ι) (isCompact_stdSimplex ι) hDisjoint
  have hLowerPos : 0 < lower := by
    simpa using hSubspace 0 subspace.zero_mem
  have hVanish : ∀ vector ∈ subspace, functional vector = 0 := by
    intro vector hVector
    by_contra hNonzero
    let scale : ℝ := (lower + 1) / functional vector
    have hScaledMem : scale • vector ∈ subspace := subspace.smul_mem scale hVector
    have hBound := hSubspace (scale • vector) hScaledMem
    have hScaled : functional (scale • vector) = lower + 1 := by
      simp only [map_smul, smul_eq_mul, scale]
      field_simp
    rw [hScaled] at hBound
    linarith
  refine ⟨functional.toLinearMap, ?_, ?_⟩
  · intro vector hVector
    exact hVanish vector hVector
  · intro i
    have hBasis := hSimplex (Pi.single i 1) (single_mem_stdSimplex ℝ i)
    change 0 < functional (Pi.single i 1)
    linarith

end KLocality
