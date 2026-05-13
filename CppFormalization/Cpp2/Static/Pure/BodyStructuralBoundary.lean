import CppFormalization.Cpp2.Static.WellFormed
import CppFormalization.Cpp2.Static.ScopeDiscipline
import CppFormalization.Cpp2.Core.TypeEnv

namespace Cpp

/-!
# CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary

Pure structural admission layer.

This file contains only state-independent structural facts:
* syntactic well-formedness,
* top-level break discipline,
* top-level continue discipline.

It deliberately does not import runtime state, semantics, readiness, adequacy,
or closure boundary modules.
-/

/-- State-independent structural boundary for a top-level function body. -/
structure BodyStructuralBoundary (Γ : TypeEnv) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st

/-- State-independent structural boundary for an opened block body. -/
structure BlockBodyStructuralBoundary (Γ : TypeEnv) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss

end Cpp
