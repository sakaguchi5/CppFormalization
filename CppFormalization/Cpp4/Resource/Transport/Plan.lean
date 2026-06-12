import CppFormalization.Cpp4.Resource.Transport.Core
import CppFormalization.Cpp4.Resource.Demand.Plan

/-!
# CppFormalization.Cpp4.Resource.Transport.Plan

Transport surfaces for `ControlPlan` and `PlanBlock` demands.
-/

namespace Cpp4

/-- ControlPlan demand transport surface. -/
structure PlanTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : PlanDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- PlanBlock demand transport surface. -/
structure PlanBlockTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : PlanBlockDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply ControlPlan transport to satisfied plan demands. -/
theorem plan_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : PlanDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : PlanTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

/-- Apply PlanBlock transport to satisfied block demands. -/
theorem plan_block_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : PlanBlockDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : PlanBlockTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

end Cpp4
