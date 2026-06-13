import CppFormalization.Cpp4.Boundary.Transport.Switch.Frame

/-!
# CppFormalization.Cpp4.Boundary.Transport.Switch.Suffix

Boundary transport for already-selected switch suffixes.
-/

namespace Cpp4

/-- Transport for one switch arm body before falling through to the remaining suffix. -/
structure SwitchArmBodyBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {arm arm' : SwitchPlanArm}
    (beforeArm : SwitchPlanArmTyping Γ κ arm)
    (afterArm : SwitchPlanArmTyping Γ' κ' arm') : Type where
  preserves :
    EffectPreservesDemand χ χ' σ σ' eff beforeArm.demand.demands afterArm.demand.demands

namespace SwitchArmBodyBoundaryTransport

/-- Apply switch-arm-body boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {arm arm' : SwitchPlanArm}
    {beforeArm : SwitchPlanArmTyping Γ κ arm}
    {afterArm : SwitchPlanArmTyping Γ' κ' arm'}
    (bArm : SwitchArmBoundary χ σ beforeArm)
    (t : SwitchArmBodyBoundaryTransport χ χ' σ σ' eff beforeArm afterArm) :
    SwitchArmBoundary χ' σ' afterArm where
  demandsSatisfied := demand_transport bArm.demandsSatisfied t.preserves

end SwitchArmBodyBoundaryTransport

/-- Fallthrough transport from a completed arm body to the rest of the selected suffix. -/
structure SwitchFallthroughBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {rest rest' : SwitchPlanArmList}
    (beforeRest : SwitchPlanArmListTyping Γ κ rest)
    (afterRest : SwitchPlanArmListTyping Γ' κ' rest') : Type where
  restTransport : SwitchArmListBoundaryTransport χ χ' σ σ' eff beforeRest afterRest

namespace SwitchFallthroughBoundaryTransport

/-- Apply fallthrough-rest boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {rest rest' : SwitchPlanArmList}
    {beforeRest : SwitchPlanArmListTyping Γ κ rest}
    {afterRest : SwitchPlanArmListTyping Γ' κ' rest'}
    (bRest : SwitchArmListBoundary χ σ beforeRest)
    (t : SwitchFallthroughBoundaryTransport χ χ' σ σ' eff beforeRest afterRest) :
    SwitchArmListBoundary χ' σ' afterRest :=
  SwitchArmListBoundaryTransport.apply bRest t.restTransport

end SwitchFallthroughBoundaryTransport

/-- Break capture in a selected switch suffix transports to an enclosing normal continuation. -/
structure SwitchBreakCaptureBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {afterPlan afterPlan' : ControlPlan}
    (beforeAfter : PlanTyping Γ κ afterPlan)
    (afterAfter : PlanTyping Γ' κ' afterPlan') : Type where
  continuationTransport : PlanBoundaryTransport χ χ' σ σ' eff beforeAfter afterAfter

namespace SwitchBreakCaptureBoundaryTransport

/-- Apply switch-break-capture continuation transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {afterPlan afterPlan' : ControlPlan}
    {beforeAfter : PlanTyping Γ κ afterPlan}
    {afterAfter : PlanTyping Γ' κ' afterPlan'}
    (b : PlanBoundary χ σ beforeAfter)
    (t : SwitchBreakCaptureBoundaryTransport χ χ' σ σ' eff beforeAfter afterAfter) :
    PlanBoundary χ' σ' afterAfter :=
  PlanBoundaryTransport.apply b t.continuationTransport

end SwitchBreakCaptureBoundaryTransport

end Cpp4
