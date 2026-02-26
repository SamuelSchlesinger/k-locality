import Cslib.Foundations.Probability.EntropyOptimization

namespace KLocality

open Cslib
open Cslib.Probability

universe u v

abbrev Distribution (α : Type u) := PMF α
abbrev Constraint (α : Type u) := LocalConstraint α
abbrev Assignment (Var : Type u) (Val : Type v) := Probability.Assignment Var Val

abbrev Feasible {α : Type u} := Probability.Feasible (α := α)
abbrev ConstraintsRespectK {α : Type u} := Probability.ConstraintsRespectK (α := α)
abbrev LocallyComplete {α : Type u} := Probability.LocallyComplete (α := α)
abbrev IsKLocal {α : Type u} := Probability.IsKLocal (α := α)

abbrev IsMarginalModel {Obs : Type u} {Lat : Type v} :=
  Probability.IsMarginalModel (Obs := Obs) (Lat := Lat)

abbrev KLocalization := Probability.KLocalization
abbrev HasKLocalization := Probability.HasKLocalization
abbrev FeasibleDistribution {α : Type u} := Probability.FeasibleDistribution (α := α)
abbrev IsMaxEntropyAmong {α : Type u} [Fintype α] := Probability.IsMaxEntropyAmong (α := α)
abbrev MarginalConstraint (Var : Type u) (Val : Type v) [DecidableEq Var] :=
  Probability.MarginalConstraint Var Val
abbrev FeasibleMarginals {Var : Type u} {Val : Type v} [DecidableEq Var] :=
  Probability.FeasibleMarginals (Var := Var) (Val := Val)
abbrev MarginalConstraintsRespectK {Var : Type u} {Val : Type v} [DecidableEq Var] :=
  Probability.MarginalConstraintsRespectK (Var := Var) (Val := Val)
abbrev MarginalLocalCompleteness {Var : Type u} {Val : Type v} [DecidableEq Var] :=
  Probability.MarginalLocalCompleteness (Var := Var) (Val := Val)
abbrev LocalSupportSet {Var : Type u} {Val : Type v} [DecidableEq Var] :=
  Probability.LocalSupportSet (Var := Var) (Val := Val)
abbrev MaximalSupport {Var : Type u} {Val : Type v} [DecidableEq Var] :=
  Probability.MaximalSupport (Var := Var) (Val := Val)
abbrev MaximalSupportHypothesis {Var : Type u} {Val : Type v} [DecidableEq Var]
    [Fintype (Assignment Var Val)] :=
  Probability.MaximalSupportHypothesis (Var := Var) (Val := Val)
abbrev IsKLocalMarginal {Var : Type u} {Val : Type v} [DecidableEq Var]
    [Fintype (Assignment Var Val)] :=
  Probability.IsKLocalMarginal (Var := Var) (Val := Val)

theorem mem_target_of_feasible
    {α : Type u} {constraints : List (Constraint α)} {target : Set α} {x : α}
    (hComplete : LocallyComplete constraints target) (hx : Feasible constraints x) :
    x ∈ target :=
  Probability.mem_target_of_feasible hComplete hx

theorem feasible_subset_target
    {α : Type u} {constraints : List (Constraint α)} {target : Set α}
    (hComplete : LocallyComplete constraints target) :
    {x | Feasible constraints x} ⊆ target :=
  Probability.feasible_subset_target hComplete

theorem feasible_eq_target
    {α : Type u} {constraints : List (Constraint α)} {target : Set α}
    (hComplete : LocallyComplete constraints target)
    (hTargetFeasible : ∀ x, x ∈ target → Feasible constraints x) :
    {x | Feasible constraints x} = target :=
  Probability.feasible_eq_target hComplete hTargetFeasible

theorem constraintsRespectK_mono
    {α : Type u} {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {constraints : List (Constraint α)} :
    ConstraintsRespectK kSmall constraints → ConstraintsRespectK kLarge constraints :=
  Probability.constraintsRespectK_mono hkl

def isKLocal_mono
    {α : Type u} {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {p : Distribution α} :
    IsKLocal kSmall p → IsKLocal kLarge p :=
  Probability.isKLocal_mono hkl

theorem hasKLocalization_mono
    {Obs : Type u} {pObs : Distribution Obs} {latentVars : Nat}
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge) :
    HasKLocalization kSmall latentVars Obs pObs → HasKLocalization kLarge latentVars Obs pObs :=
  Probability.hasKLocalization_mono hkl

def local_verification_support_level
    {α : Type u} (k : Nat) (target : Set α) (constraints : List (Constraint α))
    (hBound : ConstraintsRespectK k constraints)
    (hComplete : LocallyComplete constraints target)
    (hTargetFeasible : ∀ x, x ∈ target → Feasible constraints x)
    (p : Distribution α) (hSupport : p.support = target) :
    IsKLocal k p :=
  Probability.localVerificationSupportLevel k target constraints hBound hComplete hTargetFeasible p
    hSupport

theorem shannon_entropy_le_log_card_of_support_subset
    {α : Type u} [Fintype α]
    (p : Distribution α) (s : Finset α) (hs : s.Nonempty)
    (hsub : p.support ⊆ (s : Set α)) :
    Probability.shannonEntropy p ≤ Real.log (s.card : ℝ) :=
  Probability.shannonEntropy_le_log_card_of_support_subset p s hs hsub

theorem shannon_entropy_uniform_on
    {α : Type u} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) :
    Probability.shannonEntropy (Probability.uniformOn s hs) = Real.log (s.card : ℝ) :=
  Probability.shannonEntropy_uniformOn s hs

theorem local_verification_max_entropy_on_finset
    {α : Type u} [Fintype α] [DecidableEq α]
    (target : Finset α) (hTarget : target.Nonempty)
    (constraints : List (Constraint α))
    (hComplete : LocallyComplete constraints (target : Set α))
    (hTargetFeasible : ∀ x, x ∈ (target : Set α) → Feasible constraints x) :
    IsMaxEntropyAmong (FeasibleDistribution constraints) (Probability.uniformOn target hTarget) :=
  Probability.localVerificationMaximumEntropyOnFinset target hTarget constraints hComplete
    hTargetFeasible

theorem local_verification_max_entropy_marginals_on_finset
    {Var : Type u} {Val : Type v}
    [Fintype Var] [DecidableEq Var] [Fintype Val] [DecidableEq Val]
    (target : Finset (Assignment Var Val)) (hTarget : target.Nonempty)
    (constraints : List (MarginalConstraint Var Val))
    (hComplete : MarginalLocalCompleteness (target : Set (Assignment Var Val)) constraints)
    (hUniformFeasible : FeasibleMarginals constraints (Probability.uniformOn target hTarget)) :
    IsMaxEntropyAmong (FeasibleMarginals constraints) (Probability.uniformOn target hTarget) :=
  Probability.localVerificationMaximumEntropyMarginalsOnFinset target hTarget constraints hComplete
    hUniformFeasible

theorem support_subset_local_support_set_of_feasible_marginals
    {Var : Type u} {Val : Type v}
    [DecidableEq Var]
    {constraints : List (MarginalConstraint Var Val)}
    {q : Distribution (Assignment Var Val)}
    (hFeasible : FeasibleMarginals constraints q) :
    q.support ⊆ LocalSupportSet constraints :=
  Probability.support_subset_localSupportSet_of_feasibleMarginals hFeasible

theorem maximal_support_of_hypothesis
    {Var : Type u} {Val : Type v}
    [DecidableEq Var] [Fintype (Assignment Var Val)]
    {constraints : List (MarginalConstraint Var Val)}
    {q : Distribution (Assignment Var Val)}
    (h : MaximalSupportHypothesis constraints q) :
    MaximalSupport constraints q :=
  Probability.maximalSupport_of_hypothesis h

theorem local_verification_is_k_local_marginal_on_finset
    {Var : Type u} {Val : Type v}
    [Fintype Var] [DecidableEq Var] [Fintype Val] [DecidableEq Val]
    (k : Nat)
    (target : Finset (Assignment Var Val)) (hTarget : target.Nonempty)
    (constraints : List (MarginalConstraint Var Val))
    (hBound : MarginalConstraintsRespectK k constraints)
    (hComplete : MarginalLocalCompleteness (target : Set (Assignment Var Val)) constraints)
    (hUniformFeasible : FeasibleMarginals constraints (Probability.uniformOn target hTarget)) :
    IsKLocalMarginal k (Probability.uniformOn target hTarget) :=
  Probability.localVerificationIsKLocalMarginalOnFinset k target hTarget constraints hBound
    hComplete hUniformFeasible

noncomputable def local_verification_certificate_on_finset
    {α : Type u} [Fintype α] [DecidableEq α]
    (k : Nat) (target : Finset α) (hTarget : target.Nonempty)
    (constraints : List (Constraint α))
    (hBound : ConstraintsRespectK k constraints)
    (hComplete : LocallyComplete constraints (target : Set α))
    (hTargetFeasible : ∀ x, x ∈ (target : Set α) → Feasible constraints x) :
    PProd (IsKLocal k (Probability.uniformOn target hTarget))
      (IsMaxEntropyAmong (FeasibleDistribution constraints) (Probability.uniformOn target hTarget)) :=
  Probability.localVerificationCertificateOnFinset k target hTarget constraints hBound hComplete
    hTargetFeasible

/-- `LC_k(D)`: the minimal latent-variable count among `k`-localizations,
assuming existence. -/
noncomputable def localizationComplexity
    (k : Nat) (Obs : Type u) (pObs : Distribution Obs)
    (hExists : ∃ m, HasKLocalization k m Obs pObs) : Nat := by
  classical
  exact Nat.find hExists

theorem localizationComplexity_spec
    (k : Nat) (Obs : Type u) (pObs : Distribution Obs)
    (hExists : ∃ m, HasKLocalization k m Obs pObs) :
    HasKLocalization k (localizationComplexity k Obs pObs hExists) Obs pObs := by
  classical
  exact Nat.find_spec hExists

theorem localizationComplexity_min
    (k : Nat) (Obs : Type u) (pObs : Distribution Obs)
    (hExists : ∃ m, HasKLocalization k m Obs pObs) :
    ∀ m, HasKLocalization k m Obs pObs → localizationComplexity k Obs pObs hExists ≤ m := by
  classical
  intro m hm
  exact Nat.find_min' hExists hm

theorem localizationComplexity_mono
    {Obs : Type u} {pObs : Distribution Obs}
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    (hSmall : ∃ m, HasKLocalization kSmall m Obs pObs)
    (hLarge : ∃ m, HasKLocalization kLarge m Obs pObs) :
    localizationComplexity kLarge Obs pObs hLarge ≤ localizationComplexity kSmall Obs pObs hSmall := by
  apply localizationComplexity_min kLarge Obs pObs hLarge
  exact hasKLocalization_mono hkl (localizationComplexity_spec kSmall Obs pObs hSmall)

end KLocality
