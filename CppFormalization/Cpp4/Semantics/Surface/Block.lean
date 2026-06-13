import CppFormalization.Cpp4.Semantics.Surface.Stmt

/-!
# CppFormalization.Cpp4.Semantics.Surface.Block

Surface block semantics via expansion to `PlanBlock`.
-/

namespace Cpp4

namespace SurfaceSemantics

/-- Finite surface-block execution is finite execution of its expanded plan block. -/
def BigStepSurfaceBlock
    (χ : KernelContext) (σ : State) (b : StmtBlock) (r : CtrlResult) (σ' : State) : Prop :=
  BigStepBlock χ σ (expandBlock b) r σ'

/-- A surface block finishes normally. -/
def BigStepSurfaceBlockNormal
    (χ : KernelContext) (σ : State) (b : StmtBlock) (σ' : State) : Prop :=
  BigStepSurfaceBlock χ σ b .normal σ'

/-- A surface block exits through an abrupt control channel. -/
def BigStepSurfaceBlockAbrupt
    (χ : KernelContext) (σ : State) (b : StmtBlock) (r : CtrlResult) (σ' : State) : Prop :=
  CtrlResult.Abrupt r ∧ BigStepSurfaceBlock χ σ b r σ'

end SurfaceSemantics

end Cpp4
