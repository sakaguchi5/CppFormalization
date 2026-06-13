import CppFormalization.Cpp4.Core.Expand
import CppFormalization.Cpp4.Semantics.Kernel.Plan

/-!
# CppFormalization.Cpp4.Semantics.Surface.Stmt

Surface statement semantics via expansion to `ControlPlan`.
-/

namespace Cpp4

namespace SurfaceSemantics

/-- Finite surface-statement execution is finite execution of its expanded plan. -/
def BigStepStmt
    (χ : KernelContext) (σ : State) (s : CppStmt) (r : CtrlResult) (σ' : State) : Prop :=
  BigStepPlan χ σ (expandStmt s) r σ'

/-- A surface statement finishes normally. -/
def BigStepStmtNormal
    (χ : KernelContext) (σ : State) (s : CppStmt) (σ' : State) : Prop :=
  BigStepStmt χ σ s .normal σ'

/-- A surface statement exits through an abrupt control channel. -/
def BigStepStmtAbrupt
    (χ : KernelContext) (σ : State) (s : CppStmt) (r : CtrlResult) (σ' : State) : Prop :=
  CtrlResult.Abrupt r ∧ BigStepStmt χ σ s r σ'

end SurfaceSemantics

end Cpp4
