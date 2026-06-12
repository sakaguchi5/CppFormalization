import CppFormalization.Cpp4.Semantics.Kernel.Plan

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Block

Block-facing namespace helpers for the finite ControlPlan kernel.
-/

namespace Cpp4

namespace BigStepBlock

/-- A block finishes normally when its kernel result is `CtrlResult.normal`. -/
def Normal (χ : KernelContext) (σ : State) (b : PlanBlock) (σ' : State) : Prop :=
  BigStepBlock χ σ b .normal σ'

/-- A block exits abruptly when its kernel result is non-normal. -/
def Abrupt (χ : KernelContext) (σ : State) (b : PlanBlock) (r : CtrlResult) (σ' : State) : Prop :=
  CtrlResult.Abrupt r ∧ BigStepBlock χ σ b r σ'

end BigStepBlock

end Cpp4
