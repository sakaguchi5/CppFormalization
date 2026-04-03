import CppFormalization.Cpp2.Static.WellFormed
import CppFormalization.Cpp2.Static.ScopeDiscipline

namespace Cpp

/-!
# Closure.Foundation.BodyStructuralBoundaryLite

E-lite 補正段階の structural boundary.

方針:
- lite mainline では structural layer から old coarse typing を除去する。
- structural は本当に structural admission のみを保持する。
- typing burden は `StmtBodyProfileLite` / `BlockBodyProfileLite` 側へ集約する。

重要:
- 既存 `BodyStructuralBoundary` は legacy / compatibility 用に残す。
- こちらは lite boundary 専用の純化版である。
-/

/-- State-independent structural boundary for a top-level lite function body. -/
structure BodyStructuralBoundaryLite (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st

/-- State-independent structural boundary for an opened lite block body. -/
structure BlockBodyStructuralBoundaryLite (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss

end Cpp
