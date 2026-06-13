import CppFormalization.Cpp4.Boundary.Transport.Loop.PreTest

/-!
# CppFormalization.Cpp4.Boundary.Transport.Loop.PostTest

Boundary transport for do-while-like post-test loops.
-/

namespace Cpp4

/-- Transport from one typed post-test loop boundary to another loop boundary. -/
structure PostTestLoopBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {l l' : LoopPlan}
    (before : LoopPlanTyping Γ κ l) (after : LoopPlanTyping Γ' κ' l') : Type where
  transport : LoopTransport χ χ' σ σ' eff before.demand after.demand

namespace PostTestLoopBoundaryTransport

/-- Apply post-test loop-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {l l' : LoopPlan}
    {before : LoopPlanTyping Γ κ l} {after : LoopPlanTyping Γ' κ' l'}
    (b : LoopBoundary χ σ before)
    (t : PostTestLoopBoundaryTransport χ χ' σ σ' eff before after) :
    LoopBoundary χ' σ' after where
  demandsSatisfied := loop_transport b.demandsSatisfied t.transport

end PostTestLoopBoundaryTransport

/-- Post-test loops need to preserve the condition boundary after body normal/continue. -/
abbrev PostTestConditionBoundaryTransport := PreTestReentryBoundaryTransport

end Cpp4
