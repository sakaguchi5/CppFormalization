import CppFormalization.Cpp2.Closure.Foundation.StateBoundary

namespace Cpp.ClosureV2

/-!
# Closure.Foundation.BodyStructuralBoundary

四層分離の第1層: state に依らない structural admission boundary.

役割:
- statement / block を closure 議論に入れてよいかを表す。
- old `BodyReady` の structural 部分だけを抽出する。
-/

structure BodyStructuralBoundary (Γ : TypeEnv) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  typed0 : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st

structure BlockBodyStructuralBoundary (Γ : TypeEnv) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  typed0 : ∃ Δ, HasTypeBlock (pushTypeScope Γ) ss Δ
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss

end Cpp.ClosureV2
