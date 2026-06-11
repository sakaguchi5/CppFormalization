import CppFormalization.Cpp4.Resource.Transport.Expr

/-!
# CppFormalization.Cpp4.Resource.Transport.Stmt

Statement-demand transport surfaces.
-/

namespace Cpp4

/-- Statement-boundary transport surface.  Boundary itself will be defined above
Resource as demand satisfaction for statement syntax. -/
structure StmtTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : StmtDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply statement transport to satisfied statement demands. -/
theorem stmt_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : StmtDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : StmtTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

end Cpp4
