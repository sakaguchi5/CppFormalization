import CppFormalization.Cpp4.Semantics.Effect.Plan

/-!
# CppFormalization.Cpp4.Semantics.Effect.Block

Block-facing helpers for effect-carrying finite kernel execution.
-/

namespace Cpp4

namespace BigStepBlockWithEffect

/-- A normal effect-carrying block execution. -/
def Normal (χ : KernelContext) (σ : State) (b : PlanBlock) (σ' : State) : Type :=
  BigStepBlockWithEffect χ σ b .normal σ'

/-- An abrupt effect-carrying block execution. -/
def Abrupt (χ : KernelContext) (σ : State) (b : PlanBlock) (r : CtrlResult) (σ' : State) : Type :=
  Σ' _h : BigStepBlockWithEffect χ σ b r σ', CtrlResult.Abrupt r

end BigStepBlockWithEffect

end Cpp4
