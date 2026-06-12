import CppFormalization.Cpp4.Typing.Judgment.Plan.Plan
import CppFormalization.Cpp4.Resource.Demand.Block

/-!
# CppFormalization.Cpp4.Typing.Judgment.Plan.Block

Typing certificates for ControlPlan blocks.
-/

namespace Cpp4

/-- A typed `PlanBlock` with its ordinary-name environment effect and typed demand. -/
structure PlanBlockTyping (Γ : TypeEnv) (κ : ControlContext) (b : PlanBlock) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : PlanBlockDemand
  formation : Prop
  evidence : formation

namespace PlanBlockTyping

/-- Empty plan block. -/
def nil (Γ : TypeEnv) (κ : ControlContext) : PlanBlockTyping Γ κ .nil where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := PlanBlockDemand.nil
  formation := True
  evidence := trivial

/-- Cons a typed plan in front of a typed plan block.  The tail is typed in the
post-environment produced by the head. -/
def cons {Γ : TypeEnv} {κ : ControlContext} {head : ControlPlan} {tail : PlanBlock}
    (hHead : PlanTyping Γ κ head)
    (hTail : PlanBlockTyping hHead.target κ tail) :
    PlanBlockTyping Γ κ (.cons head tail) where
  target := hTail.target
  envEffect := TypeEnvEffect.compose hHead.envEffect hTail.envEffect
  demand := PlanBlockDemand.cons hHead.demand hTail.demand
  formation := hHead.formation ∧ hTail.formation
  evidence := And.intro hHead.evidence hTail.evidence

end PlanBlockTyping

namespace PlanTyping

/-- Scope-frame plan.  The block is checked internally, but its ordinary-name
environment effect is not exposed outside the scope frame. -/
def scopeFrame {Γ : TypeEnv} {κ : ControlContext} {b : PlanBlock}
    (hBody : PlanBlockTyping Γ κ b) : PlanTyping Γ κ (.scopeFrame b) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := PlanDemand.scopeFrame hBody.demand
  formation := hBody.formation
  evidence := hBody.evidence

end PlanTyping

end Cpp4
