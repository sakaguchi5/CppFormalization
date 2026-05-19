import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary

namespace Cpp

/-!
# CppFormalization.Cpp2.Boundary.LoopBody.StructuralBoundaryCI

Pure structural boundary for a single `while` body.

Unlike a top-level body, a loop body allows `break` and `continue`, but only as
exits scoped to the immediately enclosing loop.
-/

/-- `while` body を 1 段ぶん loop の内側で読むための break scopedness。 -/
abbrev BreakWellScopedInLoop (st : CppStmt) : Prop :=
  BreakWellScopedAt 1 st

/-- `while` body を 1 段ぶん loop の内側で読むための continue scopedness。 -/
abbrev ContinueWellScopedInLoop (st : CppStmt) : Prop :=
  ContinueWellScopedAt 1 st

/--
state-independent structural boundary for a single `while` body.

ここでは top-level body と違って `break` / `continue` を禁止しない。
代わりに「今まさに 1 段の loop の内側にいる」ことを scopedness に反映する。
-/
structure LoopBodyStructuralBoundary (Γ : TypeEnv) (body : CppStmt) : Prop where
  wf : WellFormedStmt body
  breakScoped : BreakWellScopedInLoop body
  continueScoped : ContinueWellScopedInLoop body

end Cpp
