import CppFormalization.Cpp4.Semantics.Kernel.Plan

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Switch

Switch-facing namespace helpers for the finite ControlPlan kernel.
-/

namespace Cpp4

namespace BigStepSwitchSuffix

/-- A selected switch suffix finishes normally after either fallthrough completion
or `break` capture. -/
def Normal (χ : KernelContext) (σ : State) (arms : SwitchPlanArmList) (σ' : State) : Prop :=
  BigStepSwitchSuffix χ σ arms .normal σ'

/-- A selected switch suffix may propagate `continue` or `return` to an enclosing
loop/function. -/
def Propagates (χ : KernelContext) (σ : State) (arms : SwitchPlanArmList)
    (r : CtrlResult) (σ' : State) : Prop :=
  (r = .continueResult ∨ r = .returnVoid ∨ ∃ v, r = .returnValue v) ∧
    BigStepSwitchSuffix χ σ arms r σ'

end BigStepSwitchSuffix

end Cpp4
