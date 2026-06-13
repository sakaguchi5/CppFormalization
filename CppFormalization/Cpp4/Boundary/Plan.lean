import CppFormalization.Cpp4.Boundary.Atom
import CppFormalization.Cpp4.Typing.Judgment.Plan.Switch

/-!
# CppFormalization.Cpp4.Boundary.Plan

Runtime boundaries for typed ControlPlan values.
-/

namespace Cpp4

/-- A typed ControlPlan is enterable when its generated plan demand is satisfied. -/
structure PlanBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {p : ControlPlan} (h : PlanTyping Γ κ p) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace PlanBoundary

/-- Repackage a plan boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {p : ControlPlan} {h : PlanTyping Γ κ p} (b : PlanBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a plan boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {p : ControlPlan} {h : PlanTyping Γ κ p}
    (b : DemandBoundary χ σ h.demand.demands) : PlanBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Formation evidence stored by the plan typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {p : ControlPlan} {h : PlanTyping Γ κ p} (_b : PlanBoundary χ σ h) :
    h.formation :=
  h.evidence

end PlanBoundary

end Cpp4
