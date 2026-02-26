import KLocality.Core

namespace KLocality

universe u

/-- Abstract nondeterministic support-complexity measure for a state space. -/
abbrev SupportComplexity (α : Type u) := Set α → Nat

/-- Projection hypothesis for support complexity under a set-image map. -/
def ImageProjectionBound
    {α : Type u} {β : Type u}
    (f : α → β)
    (projectionCost : Nat)
    (targetComplexity : SupportComplexity β)
    (sourceComplexity : SupportComplexity α) : Prop :=
  ∀ T : Set α, targetComplexity (f '' T) ≤ projectionCost + sourceComplexity T

/-- Compilation hypothesis specialized to local marginal-support sets:
constrained local supports can be recognized with linear cost in the number
of constraints. -/
def MarginalCompileBound
    {Var : Type u} {Val : Type u} [DecidableEq Var]
    (k Lk : Nat)
    (jointComplexity : SupportComplexity (Assignment Var Val)) : Prop :=
  ∀ constraints : List (MarginalConstraint Var Val),
    MarginalConstraintsRespectK k constraints →
      jointComplexity (LocalSupportSet constraints) ≤ constraints.length * Lk + 1

/-- Joint support-complexity upper bound from maximal support in the marginal setting. -/
theorem support_complexity_upper_bound_of_maximal_support_marginals
    {Var : Type u} {Val : Type u} [DecidableEq Var]
    {k Lk : Nat}
    (jointComplexity : SupportComplexity (Assignment Var Val))
    (hCompile : MarginalCompileBound (Var := Var) (Val := Val) (k := k) (Lk := Lk) jointComplexity)
    (constraints : List (MarginalConstraint Var Val))
    (hBound : MarginalConstraintsRespectK k constraints)
    {p : Distribution (Assignment Var Val)}
    (hMaxSupport : MaximalSupport constraints p) :
    jointComplexity p.support ≤ constraints.length * Lk + 1 := by
  rw [hMaxSupport]
  exact hCompile constraints hBound

/-- Same bound as `support_complexity_upper_bound_of_maximal_support_marginals`,
but under the paper-level maximal-support hypothesis (max entropy + support equality). -/
theorem support_complexity_upper_bound_of_maximal_support_hypothesis_marginals
    {Var : Type u} {Val : Type u}
    [DecidableEq Var] [Fintype (Assignment Var Val)]
    {k Lk : Nat}
    (jointComplexity : SupportComplexity (Assignment Var Val))
    (hCompile : MarginalCompileBound (Var := Var) (Val := Val) (k := k) (Lk := Lk) jointComplexity)
    (constraints : List (MarginalConstraint Var Val))
    (hBound : MarginalConstraintsRespectK k constraints)
    {p : Distribution (Assignment Var Val)}
    (hHyp : MaximalSupportHypothesis constraints p) :
    jointComplexity p.support ≤ constraints.length * Lk + 1 :=
  support_complexity_upper_bound_of_maximal_support_marginals
    (jointComplexity := jointComplexity)
    (hCompile := hCompile)
    constraints
    hBound
    (maximal_support_of_hypothesis hHyp)

/-- Observed support-complexity upper bound from maximal support + projection. -/
theorem support_complexity_upper_bound_observed_of_maximal_support_marginals
    {Var : Type u} {Val : Type u} [DecidableEq Var]
    {Obs : Type u}
    {k Lk projectionCost : Nat}
    (decode : Assignment Var Val → Obs)
    (obsComplexity : SupportComplexity Obs)
    (jointComplexity : SupportComplexity (Assignment Var Val))
    (hProj : ImageProjectionBound decode projectionCost obsComplexity jointComplexity)
    (hCompile : MarginalCompileBound (Var := Var) (Val := Val) (k := k) (Lk := Lk) jointComplexity)
    (constraints : List (MarginalConstraint Var Val))
    (hBound : MarginalConstraintsRespectK k constraints)
    {pJoint : Distribution (Assignment Var Val)}
    {pObs : Distribution Obs}
    (hModel : pJoint.map decode = pObs)
    (hMaxSupport : MaximalSupport constraints pJoint) :
    obsComplexity pObs.support ≤ projectionCost + (constraints.length * Lk + 1) := by
  have hSupportObs : pObs.support = decode '' pJoint.support := by
    have hmarg : pObs = pJoint.map decode := hModel.symm
    calc
      pObs.support = (pJoint.map decode).support := by simp [hmarg]
      _ = decode '' pJoint.support := by simp [PMF.support_map]
  have hProjApplied : obsComplexity pObs.support ≤ projectionCost + jointComplexity pJoint.support := by
    rw [hSupportObs]
    exact hProj pJoint.support
  have hJoint : jointComplexity pJoint.support ≤ constraints.length * Lk + 1 :=
    support_complexity_upper_bound_of_maximal_support_marginals
      (jointComplexity := jointComplexity)
      (hCompile := hCompile)
      constraints
      hBound
      hMaxSupport
  exact Nat.le_trans hProjApplied (Nat.add_le_add_left hJoint projectionCost)

/-- Observed support-complexity upper bound under the paper-level maximal-support
hypothesis (max entropy + support equality). -/
theorem support_complexity_upper_bound_observed_of_maximal_support_hypothesis_marginals
    {Var : Type u} {Val : Type u}
    [DecidableEq Var] [Fintype (Assignment Var Val)]
    {Obs : Type u}
    {k Lk projectionCost : Nat}
    (decode : Assignment Var Val → Obs)
    (obsComplexity : SupportComplexity Obs)
    (jointComplexity : SupportComplexity (Assignment Var Val))
    (hProj : ImageProjectionBound decode projectionCost obsComplexity jointComplexity)
    (hCompile : MarginalCompileBound (Var := Var) (Val := Val) (k := k) (Lk := Lk) jointComplexity)
    (constraints : List (MarginalConstraint Var Val))
    (hBound : MarginalConstraintsRespectK k constraints)
    {pJoint : Distribution (Assignment Var Val)}
    {pObs : Distribution Obs}
    (hModel : pJoint.map decode = pObs)
    (hHyp : MaximalSupportHypothesis constraints pJoint) :
    obsComplexity pObs.support ≤ projectionCost + (constraints.length * Lk + 1) :=
  support_complexity_upper_bound_observed_of_maximal_support_marginals
    (decode := decode)
    (obsComplexity := obsComplexity)
    (jointComplexity := jointComplexity)
    (hProj := hProj)
    (hCompile := hCompile)
    constraints
    hBound
    hModel
    (maximal_support_of_hypothesis hHyp)

/-- Compilation hypothesis: a family of `k`-local constraints on a joint space can be
checked by a deterministic circuit of size linear in the number of constraints, with
per-check cost `Lk`, plus one top-level aggregation gate. -/
def JointCompileBound
    {α : Type u}
    (k Lk : Nat)
    (jointComplexity : SupportComplexity α) : Prop :=
  ∀ constraints : List (Constraint α),
    ConstraintsRespectK k constraints →
      jointComplexity {x | Feasible constraints x} ≤ constraints.length * Lk + 1

/-- Projection hypothesis: existentially quantifying over `latentVars` hidden bits
adds at most `latentVars` to support complexity. -/
def ProjectionToNondetBound
    {Obs : Type u}
    (latentVars : Nat)
    (obsComplexity : SupportComplexity Obs)
    (jointComplexity : SupportComplexity (Obs × Fin latentVars)) : Prop :=
  ∀ T : Set (Obs × Fin latentVars),
    obsComplexity (Prod.fst '' T) ≤ latentVars + jointComplexity T

/-- Conditional converse bound for a concrete localization witness. -/
theorem support_complexity_upper_bound_of_kLocalization
    {Obs : Type u} {k latentVars Lk : Nat} {pObs : Distribution Obs}
    (obsComplexity : SupportComplexity Obs)
    (jointComplexity : SupportComplexity (Obs × Fin latentVars))
    (hProj : ProjectionToNondetBound latentVars obsComplexity jointComplexity)
    (hCompile : JointCompileBound (k := k) (Lk := Lk) jointComplexity)
    (loc : KLocalization k Obs (Fin latentVars) pObs) :
    obsComplexity pObs.support ≤ latentVars + (loc.kLocal.constraints.length * Lk + 1) := by
  have hSupportObs : pObs.support = Prod.fst '' loc.lifted.support := by
    have hmarg : pObs = loc.lifted.map Prod.fst := loc.marginal.symm
    calc
      pObs.support = (loc.lifted.map Prod.fst).support := by simp [hmarg]
      _ = Prod.fst '' loc.lifted.support := by
        simp [PMF.support_map]
  have hProjApplied : obsComplexity pObs.support ≤ latentVars + jointComplexity loc.lifted.support := by
    rw [hSupportObs]
    exact hProj loc.lifted.support
  have hCompileApplied :
      jointComplexity loc.lifted.support ≤ loc.kLocal.constraints.length * Lk + 1 := by
    have hFeasibleSet :
        jointComplexity {x | Feasible loc.kLocal.constraints x} ≤
          loc.kLocal.constraints.length * Lk + 1 :=
      hCompile loc.kLocal.constraints loc.kLocal.kBound
    simpa [loc.kLocal.exactSupport] using hFeasibleSet
  exact Nat.le_trans hProjApplied (Nat.add_le_add_left hCompileApplied latentVars)

/-- Constraint-count side condition used to convert witness-level converse bounds
into bounds for the minimal localization complexity witness. -/
def ConstraintCountBound
    {Obs : Type u}
    (k : Nat) (pObs : Distribution Obs)
    (bound : Nat → Nat) : Prop :=
  ∀ m (loc : KLocalization k Obs (Fin m) pObs),
    loc.kLocal.constraints.length ≤ bound m

/-- Conditional converse bound stated at the minimizer `LC_k(D)`. -/
theorem support_complexity_upper_bound_of_localizationComplexity
    {Obs : Type u} {k Lk : Nat} {pObs : Distribution Obs}
    (hExists : ∃ m, HasKLocalization k m Obs pObs)
    (obsComplexity : SupportComplexity Obs)
    (jointComplexity : (m : Nat) → SupportComplexity (Obs × Fin m))
    (hProj : ∀ m, ProjectionToNondetBound m obsComplexity (jointComplexity m))
    (hCompile : ∀ m, JointCompileBound (k := k) (Lk := Lk) (jointComplexity m))
    (bound : Nat → Nat)
    (hCount : ConstraintCountBound k pObs bound) :
    obsComplexity pObs.support ≤
      localizationComplexity k Obs pObs hExists +
        (bound (localizationComplexity k Obs pObs hExists) * Lk + 1) := by
  classical
  let m0 := localizationComplexity k Obs pObs hExists
  rcases localizationComplexity_spec k Obs pObs hExists with ⟨loc0⟩
  have hBase :
      obsComplexity pObs.support ≤ m0 + (loc0.kLocal.constraints.length * Lk + 1) :=
    support_complexity_upper_bound_of_kLocalization
      (obsComplexity := obsComplexity)
      (jointComplexity := jointComplexity m0)
      (hProj := hProj m0)
      (hCompile := hCompile m0)
      loc0
  have hLen : loc0.kLocal.constraints.length ≤ bound m0 := hCount m0 loc0
  have hMul : loc0.kLocal.constraints.length * Lk ≤ bound m0 * Lk :=
    Nat.mul_le_mul_right Lk hLen
  have hRight :
      m0 + (loc0.kLocal.constraints.length * Lk + 1) ≤ m0 + (bound m0 * Lk + 1) := by
    exact Nat.add_le_add_left (Nat.add_le_add_right hMul 1) m0
  simpa [m0] using Nat.le_trans hBase hRight

end KLocality
