import KLocality.Core

namespace KLocality

universe u

/-!
This file captures the three core circuit-to-localization connections from the
paper in a reduction-friendly way. We encode each connection as a witness
object yielding an explicit `HasKLocalization` bound.

TODO(rebuild): replace these witness-level bridges with concrete circuit
semantics from Cslib once the required foundations are added there.
-/

structure GeneratorConnection (k : Nat) (Obs : Type u) (D : Distribution Obs) where
  latentInputs : Nat
  nonOutputGates : Nat
  localization : HasKLocalization k (latentInputs + nonOutputGates) Obs D

structure FlatCircuitConnection (k : Nat) (Obs : Type u) (D : Distribution Obs) where
  gateCount : Nat
  localization : HasKLocalization k gateCount Obs D

structure WitnessCountingConnection (k : Nat) (Obs : Type u) (D : Distribution Obs) where
  witnessBits : Nat
  gateCount : Nat
  localization : HasKLocalization k (witnessBits + gateCount) Obs D

theorem generator_upper_bound
    {k : Nat} {Obs : Type u} {D : Distribution Obs}
    (h : GeneratorConnection k Obs D) :
    HasKLocalization k (h.latentInputs + h.nonOutputGates) Obs D :=
  h.localization

theorem localizationComplexity_le_generator_bound
    {k : Nat} {Obs : Type u} {D : Distribution Obs}
    (hExists : ∃ m, HasKLocalization k m Obs D)
    (h : GeneratorConnection k Obs D) :
    localizationComplexity k Obs D hExists ≤ h.latentInputs + h.nonOutputGates := by
  exact localizationComplexity_min k Obs D hExists _ h.localization

theorem flat_circuit_upper_bound
    {k : Nat} {Obs : Type u} {D : Distribution Obs}
    (h : FlatCircuitConnection k Obs D) :
    HasKLocalization k h.gateCount Obs D :=
  h.localization

theorem localizationComplexity_le_flat_bound
    {k : Nat} {Obs : Type u} {D : Distribution Obs}
    (hExists : ∃ m, HasKLocalization k m Obs D)
    (h : FlatCircuitConnection k Obs D) :
    localizationComplexity k Obs D hExists ≤ h.gateCount := by
  exact localizationComplexity_min k Obs D hExists _ h.localization

theorem witness_counting_upper_bound
    {k : Nat} {Obs : Type u} {D : Distribution Obs}
    (h : WitnessCountingConnection k Obs D) :
    HasKLocalization k (h.witnessBits + h.gateCount) Obs D :=
  h.localization

theorem localizationComplexity_le_witness_bound
    {k : Nat} {Obs : Type u} {D : Distribution Obs}
    (hExists : ∃ m, HasKLocalization k m Obs D)
    (h : WitnessCountingConnection k Obs D) :
    localizationComplexity k Obs D hExists ≤ h.witnessBits + h.gateCount := by
  exact localizationComplexity_min k Obs D hExists _ h.localization

end KLocality
