import CppFormalization.Cpp4.Boundary.Transport.Branch

/-!
# CppFormalization.Cpp4.Boundary.Transport.ScopeFrame

Boundary transport across scope-frame execution and close.
-/

namespace Cpp4

/-- Transport certificate for a scope-frame body boundary after opening a scope. -/
structure ScopeFrameBodyBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {body body' : PlanBlock}
    (beforeBody : PlanBlockTyping Γ κ body) (afterBody : PlanBlockTyping Γ' κ' body') : Type where
  bodyTransport : PlanBlockBoundaryTransport χ χ' σ σ' eff beforeBody afterBody

namespace ScopeFrameBodyBoundaryTransport

/-- Apply scope-frame body-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {body body' : PlanBlock}
    {beforeBody : PlanBlockTyping Γ κ body} {afterBody : PlanBlockTyping Γ' κ' body'}
    (bBody : PlanBlockBoundary χ σ beforeBody)
    (t : ScopeFrameBodyBoundaryTransport χ χ' σ σ' eff beforeBody afterBody) :
    PlanBlockBoundary χ' σ' afterBody :=
  PlanBlockBoundaryTransport.apply bBody t.bodyTransport

end ScopeFrameBodyBoundaryTransport

/-- Transport certificate for returning from a closed scope frame to an outer plan boundary. -/
structure ScopeFrameOuterBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {outer outer' : ControlPlan}
    (beforeOuter : PlanTyping Γ κ outer) (afterOuter : PlanTyping Γ' κ' outer') : Type where
  outerTransport : PlanBoundaryTransport χ χ' σ σ' eff beforeOuter afterOuter

namespace ScopeFrameOuterBoundaryTransport

/-- Apply outer-boundary transport after scope close. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {outer outer' : ControlPlan}
    {beforeOuter : PlanTyping Γ κ outer} {afterOuter : PlanTyping Γ' κ' outer'}
    (bOuter : PlanBoundary χ σ beforeOuter)
    (t : ScopeFrameOuterBoundaryTransport χ χ' σ σ' eff beforeOuter afterOuter) :
    PlanBoundary χ' σ' afterOuter :=
  PlanBoundaryTransport.apply bOuter t.outerTransport

end ScopeFrameOuterBoundaryTransport

end Cpp4
