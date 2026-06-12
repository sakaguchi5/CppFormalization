import CppFormalization.Cpp4.Typing.Judgment.Plan.Plan
import CppFormalization.Cpp4.Typing.Micro.ForInit
import CppFormalization.Cpp4.Typing.Micro.ForIter
import CppFormalization.Cpp4.Resource.Demand.Loop

/-!
# CppFormalization.Cpp4.Typing.Judgment.Plan.Loop

Typing certificates for `LoopPlan`.
-/

namespace Cpp4

/-- Typing certificate for an optional `for` condition. -/
inductive OptionalCondTyping (Γ : TypeEnv) : Option CppCond → Type where
  | absent : OptionalCondTyping Γ none
  | present {c : CppCond} (cond : CondTyping Γ c) :
      OptionalCondTyping Γ (some c)

namespace OptionalCondTyping

/-- Optional condition demand. -/
def demand {Γ : TypeEnv} {c : Option CppCond} :
    OptionalCondTyping Γ c → Option ExprDemand
  | .absent => none
  | .present cond => some cond.demand

/-- Formation condition for an optional condition. -/
def formation {Γ : TypeEnv} {c : Option CppCond} :
    OptionalCondTyping Γ c → Prop
  | .absent => True
  | .present cond => cond.formation

/-- Evidence for optional-condition formation. -/
def evidence {Γ : TypeEnv} {c : Option CppCond}
    (h : OptionalCondTyping Γ c) : h.formation :=
  match h with
  | .absent => trivial
  | .present cond => cond.evidence

end OptionalCondTyping

/-- A typed loop plan.  Loop-local environment effects do not escape the loop. -/
structure LoopPlanTyping (Γ : TypeEnv) (κ : ControlContext) (l : LoopPlan) : Type where
  demand : LoopDemand
  formation : Prop
  evidence : formation

namespace LoopPlanTyping

/-- While-like pre-test loop. -/
def preTest {Γ : TypeEnv} {κ : ControlContext} {c : CppCond} {body : ControlPlan}
    (hCond : CondTyping Γ c)
    (hBody : PlanTyping Γ (ControlContext.loopBody κ) body) :
    LoopPlanTyping Γ κ (.preTest c body) where
  demand := LoopDemand.preTest hCond.demand hBody.demand
  formation := hCond.formation ∧ hBody.formation
  evidence := And.intro hCond.evidence hBody.evidence

/-- Do-while-like post-test loop. -/
def postTest {Γ : TypeEnv} {κ : ControlContext} {body : ControlPlan} {c : CppCond}
    (hBody : PlanTyping Γ (ControlContext.loopBody κ) body)
    (hCond : CondTyping Γ c) :
    LoopPlanTyping Γ κ (.postTest body c) where
  demand := LoopDemand.postTest hBody.demand hCond.demand
  formation := hBody.formation ∧ hCond.formation
  evidence := And.intro hBody.evidence hCond.evidence

/-- For-like loop.  The initializer may extend the loop-local environment; the
condition, body, and iteration step are checked in that loop-local environment. -/
def forFrame {Γ : TypeEnv} {κ : ControlContext}
    {init : CppForInit} {cond : Option CppCond} {iter : CppForIter} {body : ControlPlan}
    (hInit : ForInitTyping Γ init)
    (hCond : OptionalCondTyping hInit.target cond)
    (hIter : ForIterTyping hInit.target iter)
    (hBody : PlanTyping hInit.target (ControlContext.loopBody κ) body) :
    LoopPlanTyping Γ κ (.forFrame init cond iter body) where
  demand := LoopDemand.forFrame hInit.demand hCond.demand hIter.demand hBody.demand
  formation := hInit.formation ∧ hCond.formation ∧ hIter.formation ∧ hBody.formation
  evidence :=
    And.intro hInit.evidence
      (And.intro hCond.evidence (And.intro hIter.evidence hBody.evidence))

end LoopPlanTyping

namespace PlanTyping

/-- Loop-frame plan.  Loop-local environment changes do not escape the loop. -/
def loopFrame {Γ : TypeEnv} {κ : ControlContext} {l : LoopPlan}
    (hLoop : LoopPlanTyping Γ κ l) : PlanTyping Γ κ (.loopFrame l) where
  target := Γ
  envEffect := TypeEnvEffect.id Γ
  demand := PlanDemand.loopFrame hLoop.demand
  formation := hLoop.formation
  evidence := hLoop.evidence

end PlanTyping

end Cpp4
