import CppFormalization.Cpp4.Boundary.Transport.Loop.PostTest

/-!
# CppFormalization.Cpp4.Boundary.Transport.Loop.For

Boundary transport for for-frame loops.
-/

namespace Cpp4

/-- Transport from one typed for-loop boundary to another loop boundary. -/
structure ForLoopBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {l l' : LoopPlan}
    (before : LoopPlanTyping Γ κ l) (after : LoopPlanTyping Γ' κ' l') : Type where
  transport : LoopTransport χ χ' σ σ' eff before.demand after.demand

namespace ForLoopBoundaryTransport

/-- Apply for-loop-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {l l' : LoopPlan}
    {before : LoopPlanTyping Γ κ l} {after : LoopPlanTyping Γ' κ' l'}
    (b : LoopBoundary χ σ before)
    (t : ForLoopBoundaryTransport χ χ' σ σ' eff before after) :
    LoopBoundary χ' σ' after where
  demandsSatisfied := loop_transport b.demandsSatisfied t.transport

end ForLoopBoundaryTransport

/-- For-loop reentry requires condition/body/iteration demand preservation. -/
structure ForRemainderBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {body body' : ControlPlan}
    (beforeBody : PlanTyping Γ κ body) (afterBody : PlanTyping Γ' κ' body') : Type where
  bodyTransport : PlanBoundaryTransport χ χ' σ σ' eff beforeBody afterBody

namespace ForRemainderBoundaryTransport

/-- Apply for-remainder body-boundary transport. -/
def applyBody
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {body body' : ControlPlan}
    {beforeBody : PlanTyping Γ κ body} {afterBody : PlanTyping Γ' κ' body'}
    (bBody : PlanBoundary χ σ beforeBody)
    (t : ForRemainderBoundaryTransport χ χ' σ σ' eff beforeBody afterBody) :
    PlanBoundary χ' σ' afterBody :=
  PlanBoundaryTransport.apply bBody t.bodyTransport

end ForRemainderBoundaryTransport

end Cpp4
