import CppFormalization.Cpp4.Resource.Transport.Stmt

/-!
# CppFormalization.Cpp4.Resource.Transport.Block

Block-demand transport surfaces.
-/

namespace Cpp4

/-- Block-boundary transport surface. -/
structure BlockTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : BlockDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply block transport to satisfied block demands. -/
theorem block_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : BlockDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : BlockTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

end Cpp4
