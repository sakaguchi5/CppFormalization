import CppFormalization.Cpp4.Boundary.Plan
import CppFormalization.Cpp4.Typing.Judgment.Plan.Block

/-!
# CppFormalization.Cpp4.Boundary.Block

Runtime boundaries for typed plan blocks.
-/

namespace Cpp4

/-- A typed plan block is enterable when its generated block demand is satisfied. -/
structure PlanBlockBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {b : PlanBlock} (h : PlanBlockTyping Γ κ b) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace PlanBlockBoundary

/-- Repackage a block boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {b : PlanBlock} {h : PlanBlockTyping Γ κ b} (bd : PlanBlockBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := bd.demandsSatisfied

/-- Build a block boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {b : PlanBlock} {h : PlanBlockTyping Γ κ b}
    (bd : DemandBoundary χ σ h.demand.demands) : PlanBlockBoundary χ σ h where
  demandsSatisfied := bd.satisfied

/-- Formation evidence stored by the block typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {b : PlanBlock} {h : PlanBlockTyping Γ κ b} (_bd : PlanBlockBoundary χ σ h) :
    h.formation :=
  h.evidence

end PlanBlockBoundary

end Cpp4
