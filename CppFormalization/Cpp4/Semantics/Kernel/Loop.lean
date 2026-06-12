import CppFormalization.Cpp4.Semantics.Kernel.Plan

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Loop

Loop-facing namespace helpers for the finite ControlPlan kernel.
-/

namespace Cpp4

namespace BigStepLoop

/-- A loop exits normally when break/condition handling has produced normal control. -/
def NormalExit (χ : KernelContext) (σ : State) (l : LoopPlan) (σ' : State) : Prop :=
  BigStepLoop χ σ l .normal σ'

/-- A loop propagates a return result to its enclosing function context. -/
def ReturnExit (χ : KernelContext) (σ : State) (l : LoopPlan) (r : CtrlResult) (σ' : State) : Prop :=
  (r = .returnVoid ∨ ∃ v, r = .returnValue v) ∧ BigStepLoop χ σ l r σ'

end BigStepLoop

end Cpp4
