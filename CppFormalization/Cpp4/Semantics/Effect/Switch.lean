import CppFormalization.Cpp4.Semantics.Effect.Plan

/-!
# CppFormalization.Cpp4.Semantics.Effect.Switch

Switch-facing helpers for effect-carrying finite kernel execution.
-/

namespace Cpp4

namespace BigStepSwitchSuffixWithEffect

/-- A selected switch suffix finishes normally with an explicit resource-effect trace. -/
def Normal (χ : KernelContext) (σ : State) (arms : SwitchPlanArmList) (σ' : State) : Type :=
  BigStepSwitchSuffixWithEffect χ σ arms .normal σ'

/-- A selected switch suffix propagates non-break control outward with an effect trace. -/
def Propagates (χ : KernelContext) (σ : State) (arms : SwitchPlanArmList)
    (r : CtrlResult) (σ' : State) : Type :=
  Σ' _h : BigStepSwitchSuffixWithEffect χ σ arms r σ',
    r = .continueResult ∨ r = .returnVoid ∨ ∃ v, r = .returnValue v

end BigStepSwitchSuffixWithEffect

end Cpp4
