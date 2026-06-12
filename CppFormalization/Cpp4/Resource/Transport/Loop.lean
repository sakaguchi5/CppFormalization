import CppFormalization.Cpp4.Resource.Transport.Plan
import CppFormalization.Cpp4.Resource.Demand.Loop

/-!
# CppFormalization.Cpp4.Resource.Transport.Loop

Transport surface for loop-plan demands.
-/

namespace Cpp4

/-- Loop demand transport surface. -/
structure LoopTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : LoopDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply loop transport to satisfied loop demands. -/
theorem loop_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : LoopDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : LoopTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

/-- Loop transport as plan transport through `PlanDemand.loopFrame`. -/
def loop_transport_to_plan
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : LoopDemand}
    (hT : LoopTransport χ χ' σ σ' eff before after) :
    PlanTransport χ χ' σ σ' eff
      (PlanDemand.loopFrame before) (PlanDemand.loopFrame after) := by
  constructor
  exact hT.preserves

end Cpp4
