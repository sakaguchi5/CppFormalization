import CppFormalization.Cpp4.Semantics.Surface.Function

/-!
# CppFormalization.Cpp4.Semantics.Surface.ExpandSoundness

Small bridge lemmas exposing that surface semantics is definitionally the expanded
ControlPlan semantics.
-/

namespace Cpp4

namespace SurfaceSemantics

/-- Surface statement semantics unfolds to expanded-plan semantics. -/
theorem bigStepStmt_iff_expand
    {χ : KernelContext} {σ σ' : State} {s : CppStmt} {r : CtrlResult} :
    BigStepStmt χ σ s r σ' ↔ BigStepPlan χ σ (expandStmt s) r σ' := by
  rfl

/-- Surface block semantics unfolds to expanded-plan-block semantics. -/
theorem bigStepSurfaceBlock_iff_expand
    {χ : KernelContext} {σ σ' : State} {b : StmtBlock} {r : CtrlResult} :
    BigStepSurfaceBlock χ σ b r σ' ↔ BigStepBlock χ σ (expandBlock b) r σ' := by
  rfl

end SurfaceSemantics

end Cpp4
