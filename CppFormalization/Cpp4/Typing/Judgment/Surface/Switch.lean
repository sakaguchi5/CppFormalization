import CppFormalization.Cpp4.Typing.Judgment.Surface.Block
import CppFormalization.Cpp4.Typing.Judgment.Plan.Switch

/-!
# CppFormalization.Cpp4.Typing.Judgment.Surface.Switch

Surface switch typing certificates.
-/

namespace Cpp4

namespace SwitchArmHeaderTyping

/--
Formation condition for a surface switch arm header typing certificate.

Currently this is only an existence wrapper: the header certificate has not yet
been decomposed into label/default-specific formation facts.  The `_h` argument
is intentionally unused so that this definition matches the certificate-shaped
API used by the other typing certificates.
-/
def formation {arm : SwitchArm} (_h : SwitchArmHeaderTyping arm) : Prop :=
  Nonempty (SwitchArmHeaderTyping arm)

/-- Evidence for surface switch arm header formation. -/
def evidence {arm : SwitchArm} (h : SwitchArmHeaderTyping arm) : h.formation :=
  ⟨h⟩

end SwitchArmHeaderTyping

/-- A typed surface switch arm. -/
structure SurfaceSwitchArmTyping
    (Γ : TypeEnv) (κ : ControlContext) (arm : SwitchArm) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : SwitchArmDemand
  formation : Prop
  evidence : formation

namespace SurfaceSwitchArmTyping

/-- Type a surface switch arm from its normalized label header and typed body
block. -/
def arm {Γ : TypeEnv} {κ : ControlContext} {label : SwitchLabel} {body : StmtBlock}
    (hHeader : SwitchArmHeaderTyping (.arm label body))
    (hBody : SurfaceBlockTyping Γ κ body) :
    SurfaceSwitchArmTyping Γ κ (.arm label body) where
  target := hBody.target
  envEffect := hBody.envEffect
  demand := SwitchArmDemand.body {
    demands := hBody.demand.demands
  }
  formation := hHeader.formation ∧ hBody.formation
  evidence := And.intro hHeader.evidence hBody.evidence

end SurfaceSwitchArmTyping

/-- A typed surface switch-arm list.  The list is typed in fallthrough order, so
the environment produced by one arm is available to the following suffix. -/
structure SurfaceSwitchArmListTyping
    (Γ : TypeEnv) (κ : ControlContext) (arms : SwitchArmList) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : SwitchDemand
  formation : Prop
  evidence : formation

namespace SurfaceSwitchArmListTyping

/-- Empty surface switch suffix. -/
def nil (Γ : TypeEnv) (κ : ControlContext) :
    SurfaceSwitchArmListTyping Γ κ .nil where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SwitchDemand.nil
  formation := True
  evidence := trivial

/-- Cons a typed surface arm in front of a typed fallthrough suffix. -/
def cons {Γ : TypeEnv} {κ : ControlContext} {arm : SwitchArm} {rest : SwitchArmList}
    (hArm : SurfaceSwitchArmTyping Γ κ arm)
    (hRest : SurfaceSwitchArmListTyping hArm.target κ rest) :
    SurfaceSwitchArmListTyping Γ κ (.cons arm rest) where
  target := hRest.target
  envEffect := TypeEnvEffect.compose hArm.envEffect hRest.envEffect
  demand := SwitchDemand.cons hArm.demand hRest.demand
  formation := hArm.formation ∧ hRest.formation
  evidence := And.intro hArm.evidence hRest.evidence

end SurfaceSwitchArmListTyping

namespace SurfaceSwitchTyping

/-- Surface switch statement: type the condition, then type the available
fallthrough suffixes under switch break-capture.  Arm-local ordinary-name effects
do not escape the switch statement. -/
def switchStmt {Γ : TypeEnv} {κ : ControlContext}
    {cond : CppSwitchCond} {arms : SwitchArmList}
    (hCond : SwitchCondTyping Γ cond)
    (hArms : SurfaceSwitchArmListTyping Γ (switchArmControlContext κ) arms) :
    SurfaceSwitchTyping Γ κ cond arms where
  demand := SwitchDemand.frame hCond.demand hArms.demand
  formation := hCond.formation ∧ hArms.formation
  evidence := And.intro hCond.evidence hArms.evidence

end SurfaceSwitchTyping

namespace SurfaceStmtTyping

/-- Surface switch statement as a surface statement typing certificate. -/
def switchStmt {Γ : TypeEnv} {κ : ControlContext}
    {cond : CppSwitchCond} {arms : SwitchArmList}
    (hSwitch : SurfaceSwitchTyping Γ κ cond arms) :
    SurfaceStmtTyping Γ κ (.switchStmt cond arms) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := SurfaceStmtDemand.ofPlanDemand (PlanDemand.switchFrame hSwitch.demand)
  formation := hSwitch.formation
  evidence := hSwitch.evidence

end SurfaceStmtTyping

end Cpp4
