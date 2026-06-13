import CppFormalization.Cpp4.Semantics.Divergence.Plan

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Block

Block-facing divergence helpers.
-/

namespace Cpp4

namespace DivergesBlock

/-- A nonempty block may diverge before reaching its tail. -/
def InHead (χ : KernelContext) (σ : State) (head : ControlPlan) (tail : PlanBlock) : Prop :=
  DivergesPlan χ σ head ∧ DivergesBlock χ σ (.cons head tail)

/-- A nonempty block may diverge in its tail after the head finishes normally. -/
def InTail (χ : KernelContext) (σ : State) (head : ControlPlan) (tail : PlanBlock) : Prop :=
  ∃ σ₁, BigStepPlan χ σ head .normal σ₁ ∧ DivergesBlock χ σ₁ tail

end DivergesBlock

end Cpp4
