import CppFormalization.Cpp4.Typing.Judgment.Plan.Atom
import CppFormalization.Cpp4.Resource.Demand.Plan

/-!
# CppFormalization.Cpp4.Typing.Judgment.Plan.Plan

Typing certificates for `ControlPlan` values.

The Plan judgment is the first layer that composes micro typing certificates along
ControlPlan structure.  It deliberately targets `Core.ControlPlan`, not surface
`CppStmt`, because later semantics, resource transport, boundary, and soundness
are ControlPlan-centered.
-/

namespace Cpp4

namespace CondTyping

/-- Formation side condition for a typed boolean-like control condition. -/
def formation {Γ : TypeEnv} {c : CppCond} (h : CondTyping Γ c) : Prop :=
  h.exprTyping.formation ∧ h.exprTyping.ty = .base .bool

/-- Evidence for condition formation. -/
def evidence {Γ : TypeEnv} {c : CppCond} (h : CondTyping Γ c) : h.formation :=
  And.intro h.exprTyping.evidence h.boolLike

end CondTyping

/-- A typed ControlPlan with its ordinary-name environment effect and typed demand. -/
structure PlanTyping (Γ : TypeEnv) (κ : ControlContext) (p : ControlPlan) : Type where
  target : TypeEnv
  envEffect : TypeEnvEffect Γ target
  demand : PlanDemand
  formation : Prop
  evidence : formation

namespace PlanTyping

/-- Primitive atom plan. -/
def atom {Γ : TypeEnv} {κ : ControlContext} {a : ControlAtom}
    (h : PlanAtomTyping Γ κ a) : PlanTyping Γ κ (.atom a) where
  target := h.target
  envEffect := h.envEffect
  demand := PlanDemand.atom h.demand
  formation := h.formation
  evidence := h.evidence

/-- Sequential plan composition.  The tail is typed in the post-environment of the
head. -/
def seq {Γ : TypeEnv} {κ : ControlContext} {head tail : ControlPlan}
    (hHead : PlanTyping Γ κ head)
    (hTail : PlanTyping hHead.target κ tail) :
    PlanTyping Γ κ (.seq head tail) where
  target := hTail.target
  envEffect := TypeEnvEffect.compose hHead.envEffect hTail.envEffect
  demand := PlanDemand.seq hHead.demand hTail.demand
  formation := hHead.formation ∧ hTail.formation
  evidence := And.intro hHead.evidence hTail.evidence

/-- Branch plan composition.  Branch-local environment effects are deliberately
not exposed after the branch; declarations that should persist must be sequenced
outside the branch or represented by an enclosing scope/block judgment. -/
def branch {Γ : TypeEnv} {κ : ControlContext} {c : CppCond}
    {thenPlan elsePlan : ControlPlan}
    (hCond : CondTyping Γ c)
    (hThen : PlanTyping Γ κ thenPlan)
    (hElse : PlanTyping Γ κ elsePlan) :
    PlanTyping Γ κ (.branch c thenPlan elsePlan) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := PlanDemand.branch hCond.demand hThen.demand hElse.demand
  formation := hCond.formation ∧ hThen.formation ∧ hElse.formation
  evidence := And.intro hCond.evidence (And.intro hThen.evidence hElse.evidence)

end PlanTyping

end Cpp4
