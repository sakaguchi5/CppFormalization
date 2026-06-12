import CppFormalization.Cpp4.Resource.Transport.Switch
import CppFormalization.Cpp4.Resource.Demand.Surface

/-!
# CppFormalization.Cpp4.Resource.Transport.Surface

Surface C++ transport via expanded `ControlPlan` demands.
-/

namespace Cpp4

/-- Surface statement demand transport. -/
structure SurfaceStmtTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : SurfaceStmtDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Surface block demand transport. -/
structure SurfaceBlockTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : SurfaceBlockDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Apply surface statement transport. -/
theorem surface_stmt_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : SurfaceStmtDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : SurfaceStmtTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

/-- Apply surface block transport. -/
theorem surface_block_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {before after : SurfaceBlockDemand}
    (hD : DemandSetSatisfied χ σ before.demands)
    (hT : SurfaceBlockTransport χ χ' σ σ' eff before after) :
    DemandSetSatisfied χ' σ' after.demands :=
  demand_transport hD hT.preserves

/-- Lift plan transport to surface statement transport when the surface demands
were built from the corresponding plan demands. -/
def surface_stmt_transport_of_plan
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {before after : PlanDemand}
    (hT : PlanTransport χ χ' σ σ' eff before after) :
    SurfaceStmtTransport χ χ' σ σ' eff
      (SurfaceStmtDemand.ofPlanDemand before)
      (SurfaceStmtDemand.ofPlanDemand after) := by
  constructor
  exact hT.preserves

/-- Lift plan-block transport to surface block transport. -/
def surface_block_transport_of_plan_block
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {before after : PlanBlockDemand}
    (hT : PlanBlockTransport χ χ' σ σ' eff before after) :
    SurfaceBlockTransport χ χ' σ σ' eff
      (SurfaceBlockDemand.ofPlanBlockDemand before)
      (SurfaceBlockDemand.ofPlanBlockDemand after) := by
  constructor
  exact hT.preserves

end Cpp4
