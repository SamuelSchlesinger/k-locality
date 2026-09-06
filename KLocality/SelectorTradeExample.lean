import KLocality.GroundStateExtension

namespace KLocality

universe u

/-!
# A first structured selector trade

The alternating signed measure on the three-dimensional Boolean cube kills
every monomial of degree at most two.  Its negative half is the even-parity
support and its positive half is the odd-parity complement.  This is the
smallest nontrivial instance of the cube-trade mechanism suggested by the
selector framework.
-/

/-- Parity of a three-bit assignment. -/
def parityThree (assignment : BitVec 3) : Bool :=
  xor (xor (assignment 0) (assignment 1)) (assignment 2)

/-- The four even-parity points of the three-cube. -/
def evenParityThree : Finset (BitVec 3) :=
  Finset.univ.filter fun assignment => parityThree assignment = false

theorem evenParityThree_nonempty : evenParityThree.Nonempty := by
  decide +kernel

theorem evenParityThree_card : evenParityThree.card = 4 := by
  decide +kernel

/-- Alternating rational cube trade, normalized so its positive mass on the
odd-parity complement is one. -/
def evenParityThreeTradeCoefficient
    (joint : Assignment (Sum (Fin 3) (Fin 0))) : ℚ :=
  if projectObs joint ∈ evenParityThree then -(1 / 4) else 1 / 4

/-- Above an even-parity visible point, the no-latent selector graph contains
the unique joint assignment. -/
theorem mem_noLatent_selectorGraphDistribution_of_projectObs_mem
    (selector : Selector evenParityThree (Fin 0))
    (joint : Assignment (Sum (Fin 3) (Fin 0)))
    (hVisible : projectObs joint ∈ evenParityThree) :
    joint ∈ (selectorGraphDistribution evenParityThree_nonempty selector).support := by
  let visible : evenParityThree := ⟨projectObs joint, hVisible⟩
  have hJoint : selectorGraphAssignment selector visible = joint := by
    funext coordinate
    cases coordinate with
    | inl observed => rfl
    | inr latent => exact Fin.elim0 latent
  rw [← hJoint]
  exact selectorGraphAssignment_mem_support
    evenParityThree_nonempty selector visible

/-- The normalized alternating table is a rational dual certificate for
every zero-latent selector of the even-parity support. -/
noncomputable def evenParityThreeDualCertificate
    (selector : Selector evenParityThree (Fin 0)) :
    RationalSelectorDualCertificate 2 evenParityThree_nonempty selector where
  coefficient := evenParityThreeTradeCoefficient
  momentBalance := by decide +kernel
  nonnegativeOffGraph := by
    intro joint hOffGraph
    have hOutside : projectObs joint ∉ evenParityThree := by
      intro hVisible
      exact hOffGraph
        (mem_noLatent_selectorGraphDistribution_of_projectObs_mem
          selector joint hVisible)
    simp [evenParityThreeTradeCoefficient, hOutside]
  outsideTotal := by decide +kernel

/-- The alternating three-cube trade produces genuine pairwise-moment
leakage for every zero-latent selector. -/
theorem evenParityThree_every_noLatent_selector_leaks :
    ∀ selector : Selector evenParityThree (Fin 0),
      SelectorLeaks 2 evenParityThree_nonempty selector := by
  intro selector
  exact (evenParityThreeDualCertificate selector).selectorLeaks

/-- The even-parity support needs at least one latent bit in any quadratic
ground-state extension. -/
theorem evenParityThree_groundStateExtensionComplexity_pos :
    0 < groundStateExtensionComplexity 2 3 evenParityThree := by
  exact
    (groundStateExtensionComplexity_gt_iff_every_selector_leaks
      (k := 2) (n := 3) (latentBits := 0) le_rfl
      evenParityThree evenParityThree_nonempty).2
      evenParityThree_every_noLatent_selector_leaks

/-- Consequently the uniform even-parity law is not quadratically local
without latent variables. -/
theorem evenParityThree_uniform_localizationComplexity_pos :
    0 < localizationComplexityBits 2 3
      (uniformOn evenParityThree evenParityThree_nonempty) := by
  apply lt_of_lt_of_le evenParityThree_groundStateExtensionComplexity_pos
  apply groundStateExtensionComplexity_le_localizationComplexity
    (k := 2) le_rfl
  simp

end KLocality
