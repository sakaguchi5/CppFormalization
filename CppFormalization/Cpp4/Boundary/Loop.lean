import CppFormalization.Cpp4.Boundary.Block
import CppFormalization.Cpp4.Typing.Judgment.Plan.Loop

/-!
# CppFormalization.Cpp4.Boundary.Loop

Runtime boundaries for typed loop plans.
-/

namespace Cpp4

/-- A typed loop plan is enterable when its loop demand is satisfied. -/
structure LoopBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {l : LoopPlan} (h : LoopPlanTyping Γ κ l) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace LoopBoundary

/-- Repackage a loop boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {l : LoopPlan} {h : LoopPlanTyping Γ κ l} (b : LoopBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a loop boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {l : LoopPlan} {h : LoopPlanTyping Γ κ l}
    (b : DemandBoundary χ σ h.demand.demands) : LoopBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Formation evidence stored by the loop typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {l : LoopPlan} {h : LoopPlanTyping Γ κ l} (_b : LoopBoundary χ σ h) :
    h.formation :=
  h.evidence

end LoopBoundary

end Cpp4
