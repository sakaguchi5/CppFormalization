import CppFormalization.Cpp4.Semantics.Divergence.Plan

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Switch

Switch-facing divergence helpers.
-/

namespace Cpp4

namespace DivergesSwitchSuffix

/-- A selected suffix diverges in its current arm body. -/
def InArmBody (χ : KernelContext) (σ : State)
    (label : SwitchLabel) (body : PlanBlock) (rest : SwitchPlanArmList) : Prop :=
  DivergesBlock χ σ body ∧ DivergesSwitchSuffix χ σ (.cons (.arm label body) rest)

/--
A selected suffix diverges after normal fallthrough to the rest of the suffix.

The label is intentionally unused: once the current arm body has been selected,
fallthrough-to-rest divergence depends only on the body finishing normally and
the remaining suffix diverging.  The `_label` argument is kept only to preserve
the same arm-decomposition API shape as `InArmBody`.
-/
def InFallthroughRest (χ : KernelContext) (σ : State)
    (_label : SwitchLabel) (body : PlanBlock) (rest : SwitchPlanArmList) : Prop :=
  ∃ σbody, BigStepBlock χ σ body .normal σbody ∧ DivergesSwitchSuffix χ σbody rest

end DivergesSwitchSuffix

end Cpp4
