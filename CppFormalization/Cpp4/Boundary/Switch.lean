import CppFormalization.Cpp4.Boundary.Loop
import CppFormalization.Cpp4.Typing.Judgment.Plan.Switch

/-!
# CppFormalization.Cpp4.Boundary.Switch

Runtime boundaries for typed switch frames and selected switch suffixes.
-/

namespace Cpp4

/-- A typed switch arm is enterable when its arm-body demand is satisfied. -/
structure SwitchArmBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {arm : SwitchPlanArm} (h : SwitchPlanArmTyping Γ κ arm) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace SwitchArmBoundary

/-- Repackage a switch-arm boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {arm : SwitchPlanArm} {h : SwitchPlanArmTyping Γ κ arm}
    (b : SwitchArmBoundary χ σ h) : DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a switch-arm boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {arm : SwitchPlanArm} {h : SwitchPlanArmTyping Γ κ arm}
    (b : DemandBoundary χ σ h.demand.demands) : SwitchArmBoundary χ σ h where
  demandsSatisfied := b.satisfied

end SwitchArmBoundary

/-- A typed switch-arm list is enterable when the suffix demand is satisfied. -/
structure SwitchArmListBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {arms : SwitchPlanArmList} (h : SwitchPlanArmListTyping Γ κ arms) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace SwitchArmListBoundary

/-- Repackage a switch-arm-list boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {arms : SwitchPlanArmList} {h : SwitchPlanArmListTyping Γ κ arms}
    (b : SwitchArmListBoundary χ σ h) : DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a switch-arm-list boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {arms : SwitchPlanArmList} {h : SwitchPlanArmListTyping Γ κ arms}
    (b : DemandBoundary χ σ h.demand.demands) : SwitchArmListBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Formation evidence stored by the switch-arm-list typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {arms : SwitchPlanArmList} {h : SwitchPlanArmListTyping Γ κ arms}
    (_b : SwitchArmListBoundary χ σ h) : h.formation :=
  h.evidence

end SwitchArmListBoundary

end Cpp4
