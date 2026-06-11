import CppFormalization.Cpp4.Resource.Transport.Core

/-!
# CppFormalization.Cpp4.Resource.Transport.Expr

Expression-demand transport surfaces.
-/

namespace Cpp4

/-- Expression-boundary transport surface. -/
structure ExprTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : ExprDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply expression transport to satisfied expression demands. -/
theorem expr_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : ExprDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : ExprTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

end Cpp4
