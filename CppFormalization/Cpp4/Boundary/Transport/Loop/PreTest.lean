import CppFormalization.Cpp4.Boundary.Transport.ScopeFrame
import CppFormalization.Cpp4.Boundary.Loop
import CppFormalization.Cpp4.Resource.Transport.Loop

/-!
# CppFormalization.Cpp4.Boundary.Transport.Loop.PreTest

Boundary transport for while-like pre-test loops.
-/

namespace Cpp4

/-- Transport from one typed pre-test loop boundary to another loop boundary. -/
structure PreTestLoopBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {l l' : LoopPlan}
    (before : LoopPlanTyping Γ κ l) (after : LoopPlanTyping Γ' κ' l') : Type where
  transport : LoopTransport χ χ' σ σ' eff before.demand after.demand

namespace PreTestLoopBoundaryTransport

/-- Apply pre-test loop-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {l l' : LoopPlan}
    {before : LoopPlanTyping Γ κ l} {after : LoopPlanTyping Γ' κ' l'}
    (b : LoopBoundary χ σ before)
    (t : PreTestLoopBoundaryTransport χ χ' σ σ' eff before after) :
    LoopBoundary χ' σ' after where
  demandsSatisfied := loop_transport b.demandsSatisfied t.transport

/-- View pre-test loop transport as ControlPlan transport through `loopFrame`. -/
def toPlanTransport
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {l l' : LoopPlan}
    {before : LoopPlanTyping Γ κ l} {after : LoopPlanTyping Γ' κ' l'}
    (t : PreTestLoopBoundaryTransport χ χ' σ σ' eff before after) :
    PlanTransport χ χ' σ σ' eff
      (PlanDemand.loopFrame before.demand) (PlanDemand.loopFrame after.demand) :=
  loop_transport_to_plan t.transport

end PreTestLoopBoundaryTransport

/-- The reentry condition boundary required after a normal or continue body route. -/
structure PreTestReentryBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {c c' : CppCond}
    (beforeCond : CondTyping Γ c) (afterCond : CondTyping Γ' c') : Type where
  condTransport : CondBoundaryTransport χ χ' σ σ' eff beforeCond afterCond

namespace PreTestReentryBoundaryTransport

/-- Apply reentry-condition boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {c c' : CppCond}
    {beforeCond : CondTyping Γ c} {afterCond : CondTyping Γ' c'}
    (b : CondBoundary χ σ beforeCond)
    (t : PreTestReentryBoundaryTransport χ χ' σ σ' eff beforeCond afterCond) :
    CondBoundary χ' σ' afterCond :=
  CondBoundaryTransport.apply b t.condTransport

end PreTestReentryBoundaryTransport

end Cpp4
