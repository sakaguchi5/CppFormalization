import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Core.Fragment

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureConcrete

`InternalClosureRoadmapConcrete` までで theorem-backed になった concrete kernel を前提に、
function-body closure の残り open obligations を concrete 側で固定する層。

このファイルの役割は 2 つ:
- 既に theorem-backed な concrete normal-preservation / residual-readiness を closure 主線から読む。
- まだ未証明の function-body case split obligations を、必要最小限の形で切り出す。

ここでは abstract roadmap には戻らない。
-/

/-- Primitive core statements are the statement forms whose closure should reduce to
expr/place progress and primitive preservation alone. -/
def PrimitiveCoreStmtConcrete : CppStmt → Prop
  | .skip => True
  | .exprStmt _ => True
  | .assign _ _ => True
  | .declareObj _ _ _ => True
  | .declareRef _ _ _ => True
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt _ => True
  | .seq _ _ => False
  | .ite _ _ _ => False
  | .whileStmt _ _ => False
  | .block _ => False

 theorem PrimitiveCoreStmtConcrete.core
    {st : CppStmt} :
    PrimitiveCoreStmtConcrete st → CoreBigStepFragment st := by
  intro h
  cases st <;> simp [PrimitiveCoreStmtConcrete, CoreBigStepFragment, InBigStepFragment] at h ⊢

/-- At function-body top level, `break` and `continue` are excluded by the existing
scope-discipline theorems packaged inside `BodyReady`. -/
theorem top_level_abrupt_excluded_from_bodyReady_concrete
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyReady Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact stmt_break_not_scoped hbreak hready.breakScoped
  · intro hcont
    exact stmt_continue_not_scoped hcont hready.continueScoped

end Cpp
