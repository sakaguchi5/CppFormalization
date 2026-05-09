import CppFormalization.Cpp2.Closure.Foundation.CoreBigStepFragment

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosure

内部主定理
`concrete_body_ready_function_body_progress_or_diverges`
を statement 形ごとの case に分解する青写真。

ポイント:
- closure theorem の主役は raw stmt ではなく function-body 側。
- `break/continue` 漏れは既存 `ControlExclusion` に任せる。
- ここでは各 statement 形ごとに、何を示せば最終定理に到達できるかを固定する。
-/

def PrimitiveCoreStmt : CppStmt → Prop
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

theorem PrimitiveCoreStmt.core
    {st : CppStmt} :
    PrimitiveCoreStmt st → CoreBigStepFragment st := by
  intro h
  cases st <;> simp [PrimitiveCoreStmt, CoreBigStepFragment, InBigStepFragment] at h ⊢

end Cpp
