import CppFormalization.Cpp4.Resource.Certification.Abstract
import CppFormalization.Cpp4.Semantics.Effect.All

/-!
# CppFormalization.Cpp4.Semantics.Certification.Effect

Semantics-side effect-footprint extraction for B.

This file does not strengthen the current effect-carrying semantics.  It fixes the
place where `BigStep...WithEffect` witnesses are converted into the resource
certification pipeline's effect footprint.  Later B-theorems should strengthen the
construction of those `WithEffect` witnesses, not Boundary.Transport.
-/

namespace Cpp4

namespace BigStepAtomWithEffect

/-- Effect footprint exposed by a finite atom step with effect. -/
def effectFootprint {χ : KernelContext} {σ σ' : State} {a : ControlAtom} {r : CtrlResult}
    (h : BigStepAtomWithEffect χ σ a r σ') : EffectFootprint σ σ' :=
  GeneratedEffect.ofTrace h.trace

end BigStepAtomWithEffect

namespace BigStepPlanWithEffect

/-- Effect footprint exposed by a finite ControlPlan step with effect. -/
def effectFootprint {χ : KernelContext} {σ σ' : State} {p : ControlPlan} {r : CtrlResult}
    (h : BigStepPlanWithEffect χ σ p r σ') : EffectFootprint σ σ' :=
  GeneratedEffect.ofTrace h.trace

end BigStepPlanWithEffect

namespace BigStepBlockWithEffect

/-- Effect footprint exposed by a finite plan-block step with effect. -/
def effectFootprint {χ : KernelContext} {σ σ' : State} {b : PlanBlock} {r : CtrlResult}
    (h : BigStepBlockWithEffect χ σ b r σ') : EffectFootprint σ σ' :=
  GeneratedEffect.ofTrace h.trace

end BigStepBlockWithEffect

namespace BigStepLoopWithEffect

/-- Effect footprint exposed by a finite loop step with effect. -/
def effectFootprint {χ : KernelContext} {σ σ' : State} {l : LoopPlan} {r : CtrlResult}
    (h : BigStepLoopWithEffect χ σ l r σ') : EffectFootprint σ σ' :=
  GeneratedEffect.ofTrace h.trace

end BigStepLoopWithEffect

namespace BigStepSwitchSuffixWithEffect

/-- Effect footprint exposed by a finite switch-suffix step with effect. -/
def effectFootprint {χ : KernelContext} {σ σ' : State} {arms : SwitchPlanArmList} {r : CtrlResult}
    (h : BigStepSwitchSuffixWithEffect χ σ arms r σ') : EffectFootprint σ σ' :=
  GeneratedEffect.ofTrace h.trace

end BigStepSwitchSuffixWithEffect

end Cpp4
