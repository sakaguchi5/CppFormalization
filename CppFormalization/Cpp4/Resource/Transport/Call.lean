import CppFormalization.Cpp4.Resource.Transport.Block

/-!
# CppFormalization.Cpp4.Resource.Transport.Call

Call-demand transport surfaces.
-/

namespace Cpp4

/-- Call-continuation transport surface. -/
structure CallTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : CallDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply call transport to satisfied call demands. -/
theorem call_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : CallDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : CallTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

end Cpp4
