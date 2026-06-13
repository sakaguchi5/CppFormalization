import CppFormalization.Cpp4.Semantics.Effect.Plan

/-!
# CppFormalization.Cpp4.Semantics.Effect.Loop

Loop-facing helpers for effect-carrying finite kernel execution.
-/

namespace Cpp4

namespace BigStepLoopWithEffect

/-- A loop exits normally with an explicit resource-effect trace. -/
def NormalExit (χ : KernelContext) (σ : State) (l : LoopPlan) (σ' : State) : Type :=
  BigStepLoopWithEffect χ σ l .normal σ'

/-- A loop propagates a function-return channel with an explicit resource-effect trace. -/
def ReturnExit (χ : KernelContext) (σ : State) (l : LoopPlan) (r : CtrlResult) (σ' : State) : Type :=
  Σ' _h : BigStepLoopWithEffect χ σ l r σ', r = .returnVoid ∨ ∃ v, r = .returnValue v

end BigStepLoopWithEffect

end Cpp4
