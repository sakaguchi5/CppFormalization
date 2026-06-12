import CppFormalization.Cpp4.Resource.Transport.Loop
import CppFormalization.Cpp4.Resource.Demand.Switch

/-!
# CppFormalization.Cpp4.Resource.Transport.Switch

Transport surfaces for switch-frame and selected-switch-suffix demands.
-/

namespace Cpp4

/-- Switch demand transport surface. -/
structure SwitchTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : SwitchDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply switch transport to satisfied switch demands. -/
theorem switch_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : SwitchDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : SwitchTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

/-- Switch-frame transport as plan transport. -/
def switch_frame_transport_to_plan
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : SwitchDemand}
    (hT : SwitchTransport χ χ' σ σ' eff before after) :
    PlanTransport χ χ' σ σ' eff
      (PlanDemand.switchFrame before) (PlanDemand.switchFrame after) := by
  constructor
  exact hT.preserves

/-- Selected switch-suffix transport as plan transport. -/
def switch_suffix_transport_to_plan
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : SwitchDemand}
    (hT : SwitchTransport χ χ' σ σ' eff before after) :
    PlanTransport χ χ' σ σ' eff
      (PlanDemand.switchSuffix before) (PlanDemand.switchSuffix after) := by
  constructor
  exact hT.preserves

end Cpp4
