import CppFormalization.Cpp4.Typing.Judgment.Plan.Block
import CppFormalization.Cpp4.Typing.Micro.Switch
import CppFormalization.Cpp4.Resource.Demand.Switch

/-!
# CppFormalization.Cpp4.Typing.Judgment.Plan.Switch

Typing certificates for ControlPlan switch frames and selected switch suffixes.
-/

namespace Cpp4

namespace SwitchCondTyping

/-- Formation condition for a typed switch condition. -/
def formation {Γ : TypeEnv} {c : CppSwitchCond} (h : SwitchCondTyping Γ c) : Prop :=
  h.exprTyping.formation ∧ h.exprTyping.ty = .base .int

/-- Evidence for switch-condition formation. -/
def evidence {Γ : TypeEnv} {c : CppSwitchCond} (h : SwitchCondTyping Γ c) :
    h.formation :=
  And.intro h.exprTyping.evidence h.integral

end SwitchCondTyping

namespace SwitchPlanArmHeaderTyping

/-- Formation condition for a switch arm header typing certificate. -/
def formation {arm : SwitchPlanArm} (_h : SwitchPlanArmHeaderTyping arm) : Prop :=
  Nonempty (SwitchPlanArmHeaderTyping arm)

/-- Evidence for switch arm header formation. -/
def evidence {arm : SwitchPlanArm}
    (h : SwitchPlanArmHeaderTyping arm) : h.formation :=
  ⟨h⟩

end SwitchPlanArmHeaderTyping

/-- A typed ControlPlan switch arm. -/
structure SwitchPlanArmTyping
    (Γ : TypeEnv) (κ : ControlContext) (arm : SwitchPlanArm) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : SwitchArmDemand
  formation : Prop
  evidence : formation

namespace SwitchPlanArmTyping

/-- Type a switch arm from its normalized label header and typed body block. -/
def arm {Γ : TypeEnv} {κ : ControlContext} {label : SwitchLabel} {body : PlanBlock}
    (hHeader : SwitchPlanArmHeaderTyping (.arm label body))
    (hBody : PlanBlockTyping Γ κ body) :
    SwitchPlanArmTyping Γ κ (.arm label body) where
  target := hBody.target
  envEffect := hBody.envEffect
  demand := SwitchArmDemand.body hBody.demand
  formation := hHeader.formation ∧ hBody.formation
  evidence := And.intro hHeader.evidence hBody.evidence

end SwitchPlanArmTyping

/-- A typed switch-arm list.  The list is typed in fallthrough order, so the
environment produced by one arm is available to the following suffix. -/
structure SwitchPlanArmListTyping
    (Γ : TypeEnv) (κ : ControlContext) (arms : SwitchPlanArmList) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : SwitchDemand
  formation : Prop
  evidence : formation

namespace SwitchPlanArmListTyping

/-- Empty switch suffix. -/
def nil (Γ : TypeEnv) (κ : ControlContext) :
    SwitchPlanArmListTyping Γ κ .nil where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SwitchDemand.nil
  formation := True
  evidence := trivial

/-- Cons a typed arm in front of a typed fallthrough suffix. -/
def cons {Γ : TypeEnv} {κ : ControlContext}
    {arm : SwitchPlanArm} {rest : SwitchPlanArmList}
    (hArm : SwitchPlanArmTyping Γ κ arm)
    (hRest : SwitchPlanArmListTyping hArm.target κ rest) :
    SwitchPlanArmListTyping Γ κ (.cons arm rest) where
  target := hRest.target
  envEffect := TypeEnvEffect.compose hArm.envEffect hRest.envEffect
  demand := SwitchDemand.cons hArm.demand hRest.demand
  formation := hArm.formation ∧ hRest.formation
  evidence := And.intro hArm.evidence hRest.evidence

end SwitchPlanArmListTyping

namespace PlanTyping

/-- Normalized switch frame: type the condition, then type the available arm
suffixes under switch break-capture.  Arm-local environment effects do not escape
the switch frame. -/
def switchFrame {Γ : TypeEnv} {κ : ControlContext}
    {cond : CppSwitchCond} {arms : SwitchPlanArmList}
    (hCond : SwitchCondTyping Γ cond)
    (hArms : SwitchPlanArmListTyping Γ (switchArmControlContext κ) arms) :
    PlanTyping Γ κ (.switchFrame cond arms) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := PlanDemand.switchFrame (SwitchDemand.frame hCond.demand hArms.demand)
  formation := hCond.formation ∧ hArms.formation
  evidence := And.intro hCond.evidence hArms.evidence

/-- Already-selected switch suffix.  It is checked under switch break-capture, and
its local environment effects do not escape the suffix plan. -/
def switchSuffix {Γ : TypeEnv} {κ : ControlContext} {arms : SwitchPlanArmList}
    (hArms : SwitchPlanArmListTyping Γ (switchArmControlContext κ) arms) :
    PlanTyping Γ κ (.switchSuffix arms) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := PlanDemand.switchSuffix (SwitchDemand.suffix hArms.demand)
  formation := hArms.formation
  evidence := hArms.evidence

end PlanTyping

end Cpp4
