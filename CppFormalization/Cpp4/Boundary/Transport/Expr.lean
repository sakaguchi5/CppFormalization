import CppFormalization.Cpp4.Boundary.Transport.Place
import CppFormalization.Cpp4.Boundary.Expr
import CppFormalization.Cpp4.Resource.Transport.Expr

/-!
# CppFormalization.Cpp4.Boundary.Transport.Expr

Transport for runtime boundaries of typed value expressions and conditions.
-/

namespace Cpp4

/-- Transport from one typed-expression boundary to another. -/
structure ExprBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {e e' : ValExpr}
    (before : ExprTyping Γ e) (after : ExprTyping Γ' e') : Type where
  transport : ExprTransport χ χ' σ σ' eff before.demand after.demand

namespace ExprBoundaryTransport

/-- Apply expression-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {e e' : ValExpr}
    {before : ExprTyping Γ e} {after : ExprTyping Γ' e'}
    (b : ExprBoundary χ σ before)
    (t : ExprBoundaryTransport χ χ' σ σ' eff before after) :
    ExprBoundary χ' σ' after where
  demandsSatisfied := expr_transport b.demandsSatisfied t.transport

/-- Build expression-boundary transport from a raw preservation certificate. -/
def ofPreserves
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {e e' : ValExpr}
    {before : ExprTyping Γ e} {after : ExprTyping Γ' e'}
    (h : EffectPreservesDemand χ χ' σ σ' eff before.demand.demands after.demand.demands) :
    ExprBoundaryTransport χ χ' σ σ' eff before after where
  transport := { preserves := h }

end ExprBoundaryTransport

/-- Transport from one typed-condition boundary to another. -/
structure CondBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {c c' : CppCond}
    (before : CondTyping Γ c) (after : CondTyping Γ' c') : Type where
  preserves :
    EffectPreservesDemand χ χ' σ σ' eff before.demand.demands after.demand.demands

namespace CondBoundaryTransport

/-- Apply condition-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {c c' : CppCond}
    {before : CondTyping Γ c} {after : CondTyping Γ' c'}
    (b : CondBoundary χ σ before)
    (t : CondBoundaryTransport χ χ' σ σ' eff before after) :
    CondBoundary χ' σ' after where
  demandsSatisfied := demand_transport b.demandsSatisfied t.preserves

end CondBoundaryTransport

end Cpp4
