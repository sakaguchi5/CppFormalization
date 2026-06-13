import CppFormalization.Cpp4.Semantics.Divergence.Plan

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Loop

Loop-facing divergence helpers.
-/

namespace Cpp4

namespace DivergesLoop

/-- A pre-test loop diverges in guard evaluation, in body execution, or in reentry. -/
def PreTest (χ : KernelContext) (σ : State) (c : CppCond) (body : ControlPlan) : Prop :=
  DivergesLoop χ σ (.preTest c body)

/-- A post-test loop diverges in body evaluation, guard evaluation, or reentry. -/
def PostTest (χ : KernelContext) (σ : State) (body : ControlPlan) (c : CppCond) : Prop :=
  DivergesLoop χ σ (.postTest body c)

/-- A for-loop diverges either in initialization or in the loop remainder. -/
def ForFrame (χ : KernelContext) (σ : State)
    (init : CppForInit) (cond : Option CppCond) (iter : CppForIter) (body : ControlPlan) : Prop :=
  DivergesLoop χ σ (.forFrame init cond iter body)

end DivergesLoop

end Cpp4
