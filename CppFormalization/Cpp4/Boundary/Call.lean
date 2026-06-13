import CppFormalization.Cpp4.Boundary.Expr

/-!
# CppFormalization.Cpp4.Boundary.Call

Runtime boundaries for typed function calls.
-/

namespace Cpp4

/-- A typed call is enterable when the callable and its argument demands are satisfied. -/
structure CallBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {Φ : FunctionEnv}
    {f : FunctionName} {args : CallArgs}
    (h : CallTyping Γ Φ f args) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace CallBoundary

/-- Repackage a call boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {Φ : FunctionEnv}
    {f : FunctionName} {args : CallArgs} {h : CallTyping Γ Φ f args}
    (b : CallBoundary χ σ h) : DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a call boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {Φ : FunctionEnv}
    {f : FunctionName} {args : CallArgs} {h : CallTyping Γ Φ f args}
    (b : DemandBoundary χ σ h.demand.demands) : CallBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- The callable declaration used by the call typing certificate. -/
def callableDecl {χ : DemandContext} {σ : State} {Γ : TypeEnv} {Φ : FunctionEnv}
    {f : FunctionName} {args : CallArgs} {h : CallTyping Γ Φ f args}
    (_b : CallBoundary χ σ h) : CallableDecl :=
  h.decl

end CallBoundary

end Cpp4
