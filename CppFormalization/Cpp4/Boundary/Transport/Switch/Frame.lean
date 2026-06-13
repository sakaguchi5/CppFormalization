import CppFormalization.Cpp4.Boundary.Transport.Loop.For
import CppFormalization.Cpp4.Boundary.Switch
import CppFormalization.Cpp4.Resource.Transport.Switch

/-!
# CppFormalization.Cpp4.Boundary.Transport.Switch.Frame

Boundary transport for normalized switch frames.
-/

namespace Cpp4

/-- Transport from one typed switch-arm-list boundary to another. -/
structure SwitchArmListBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {arms arms' : SwitchPlanArmList}
    (before : SwitchPlanArmListTyping Γ κ arms)
    (after : SwitchPlanArmListTyping Γ' κ' arms') : Type where
  transport : SwitchTransport χ χ' σ σ' eff before.demand after.demand

namespace SwitchArmListBoundaryTransport

/-- Apply switch-arm-list boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {arms arms' : SwitchPlanArmList}
    {before : SwitchPlanArmListTyping Γ κ arms}
    {after : SwitchPlanArmListTyping Γ' κ' arms'}
    (b : SwitchArmListBoundary χ σ before)
    (t : SwitchArmListBoundaryTransport χ χ' σ σ' eff before after) :
    SwitchArmListBoundary χ' σ' after where
  demandsSatisfied := switch_transport b.demandsSatisfied t.transport

end SwitchArmListBoundaryTransport

/-- Transport for the selected suffix after switch condition/case selection. -/
structure SwitchFrameSelectedSuffixTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {suffix suffix' : SwitchPlanArmList}
    (beforeSuffix : SwitchPlanArmListTyping Γ κ suffix)
    (afterSuffix : SwitchPlanArmListTyping Γ' κ' suffix') : Type where
  suffixTransport : SwitchArmListBoundaryTransport χ χ' σ σ' eff beforeSuffix afterSuffix

namespace SwitchFrameSelectedSuffixTransport

/-- Apply selected-switch-suffix transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {suffix suffix' : SwitchPlanArmList}
    {beforeSuffix : SwitchPlanArmListTyping Γ κ suffix}
    {afterSuffix : SwitchPlanArmListTyping Γ' κ' suffix'}
    (bSuffix : SwitchArmListBoundary χ σ beforeSuffix)
    (t : SwitchFrameSelectedSuffixTransport χ χ' σ σ' eff beforeSuffix afterSuffix) :
    SwitchArmListBoundary χ' σ' afterSuffix :=
  SwitchArmListBoundaryTransport.apply bSuffix t.suffixTransport

end SwitchFrameSelectedSuffixTransport

end Cpp4
