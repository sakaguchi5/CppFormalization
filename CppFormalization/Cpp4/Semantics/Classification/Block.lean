import CppFormalization.Cpp4.Semantics.Classification.Plan

/-!
# CppFormalization.Cpp4.Semantics.Classification.Block

Block-facing classification helpers.
-/

namespace Cpp4

namespace BlockClassification

/-- A normal finite block classification. -/
def finiteNormal {χ : KernelContext} {σ σ' : State} {b : PlanBlock}
    (h : BigStepBlock χ σ b .normal σ') : BlockClassification χ σ b :=
  .finite h

/-- A divergent block classification. -/
def ofDivergence {χ : KernelContext} {σ : State} {b : PlanBlock}
    (h : DivergesBlock χ σ b) : BlockClassification χ σ b :=
  .diverges h

end BlockClassification

end Cpp4
