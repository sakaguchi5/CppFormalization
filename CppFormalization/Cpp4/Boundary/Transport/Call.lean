import CppFormalization.Cpp4.Boundary.Transport.Expr
import CppFormalization.Cpp4.Boundary.Call
import CppFormalization.Cpp4.Resource.Transport.Call

/-!
# CppFormalization.Cpp4.Boundary.Transport.Call

Transport for runtime boundaries of typed function calls.
-/

namespace Cpp4

/-- Transport from one typed-call boundary to another. -/
structure CallBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {Φ Φ' : FunctionEnv}
    {f f' : FunctionName} {args args' : CallArgs}
    (before : CallTyping Γ Φ f args) (after : CallTyping Γ' Φ' f' args') : Type where
  transport : CallTransport χ χ' σ σ' eff before.demand after.demand

namespace CallBoundaryTransport

/-- Apply call-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {Φ Φ' : FunctionEnv}
    {f f' : FunctionName} {args args' : CallArgs}
    {before : CallTyping Γ Φ f args} {after : CallTyping Γ' Φ' f' args'}
    (b : CallBoundary χ σ before)
    (t : CallBoundaryTransport χ χ' σ σ' eff before after) :
    CallBoundary χ' σ' after where
  demandsSatisfied := call_transport b.demandsSatisfied t.transport

/-- Build call-boundary transport from a raw preservation certificate. -/
def ofPreserves
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {Φ Φ' : FunctionEnv}
    {f f' : FunctionName} {args args' : CallArgs}
    {before : CallTyping Γ Φ f args} {after : CallTyping Γ' Φ' f' args'}
    (h : EffectPreservesDemand χ χ' σ σ' eff before.demand.demands after.demand.demands) :
    CallBoundaryTransport χ χ' σ σ' eff before after where
  transport := { preserves := h }

end CallBoundaryTransport

end Cpp4
