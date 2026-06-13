import CppFormalization.Cpp4.Semantics.Effect.Atom
import CppFormalization.Cpp4.Semantics.Kernel.Plan

/-!
# CppFormalization.Cpp4.Semantics.Effect.Plan

Effect-carrying wrappers for finite ControlPlan kernel execution.
-/

namespace Cpp4

structure BigStepPlanWithEffect
    (χ : KernelContext) (σ : State) (p : ControlPlan) (r : CtrlResult) (σ' : State) : Type where
  step : BigStepPlan χ σ p r σ'
  trace : EffectTrace σ σ'

structure BigStepBlockWithEffect
    (χ : KernelContext) (σ : State) (b : PlanBlock) (r : CtrlResult) (σ' : State) : Type where
  step : BigStepBlock χ σ b r σ'
  trace : EffectTrace σ σ'

structure BigStepLoopWithEffect
    (χ : KernelContext) (σ : State) (l : LoopPlan) (r : CtrlResult) (σ' : State) : Type where
  step : BigStepLoop χ σ l r σ'
  trace : EffectTrace σ σ'

structure BigStepForRemainderWithEffect
    (χ : KernelContext) (σ : State) (cond : Option CppCond) (iter : CppForIter)
    (body : ControlPlan) (r : CtrlResult) (σ' : State) : Type where
  step : BigStepForRemainder χ σ cond iter body r σ'
  trace : EffectTrace σ σ'

structure BigStepSwitchSuffixWithEffect
    (χ : KernelContext) (σ : State) (arms : SwitchPlanArmList) (r : CtrlResult) (σ' : State) : Type where
  step : BigStepSwitchSuffix χ σ arms r σ'
  trace : EffectTrace σ σ'

namespace BigStepPlanWithEffect

/-- Attach an already chosen resource-effect trace to a plan step. -/
def attach {χ : KernelContext} {σ σ' : State} {p : ControlPlan} {r : CtrlResult}
    (step : BigStepPlan χ σ p r σ') (effect : ResourceEffect) :
    BigStepPlanWithEffect χ σ p r σ' where
  step := step
  trace := { effect := effect }

/-- Forget the resource-effect trace. -/
def forget {χ : KernelContext} {σ σ' : State} {p : ControlPlan} {r : CtrlResult}
    (h : BigStepPlanWithEffect χ σ p r σ') : BigStepPlan χ σ p r σ' :=
  h.step

end BigStepPlanWithEffect

namespace BigStepBlockWithEffect

/-- Attach an already chosen resource-effect trace to a block step. -/
def attach {χ : KernelContext} {σ σ' : State} {b : PlanBlock} {r : CtrlResult}
    (step : BigStepBlock χ σ b r σ') (effect : ResourceEffect) :
    BigStepBlockWithEffect χ σ b r σ' where
  step := step
  trace := { effect := effect }

/-- Forget the resource-effect trace. -/
def forget {χ : KernelContext} {σ σ' : State} {b : PlanBlock} {r : CtrlResult}
    (h : BigStepBlockWithEffect χ σ b r σ') : BigStepBlock χ σ b r σ' :=
  h.step

end BigStepBlockWithEffect

end Cpp4
