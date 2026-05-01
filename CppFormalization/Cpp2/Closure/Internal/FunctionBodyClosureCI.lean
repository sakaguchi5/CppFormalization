import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Closure.Internal.CurrentShellCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyReplayStablePrimitiveWhileFacts
import CppFormalization.Cpp2.Boundary.FunctionBody

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureCI

CI-centric function-body closure layer.

目的:
- old `BodyReady` を主線から降格し、internal closure の driver を `BodyReadyCI` に移す。
- 既存 concrete kernel (`StmtControlPreservation`, `ReadinessBoundaryConcrete`,
  `InternalClosureRoadmapConcrete`) はそのまま利用する。
- replay-stable primitive `while` special case は
  `FunctionBodyReplayStablePrimitiveWhileFacts.lean` に分離した。
- live な shell は canonical `BodyClosureBoundaryCI` surface の
  global recursion principle だけに縮めた。
  `BodyReadyCI` entry theorem は forgetful map `toClosureBoundary` から導く。
-/

/-
Current live shell was shrunk to a global recursion principle in `CurrentShellCI.lean`.
-/

/-- canonical entry theorem for function-body closure. -/
theorem body_closure_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hentry
  exact body_closure_ci_function_body_global_recursion hfrag hentry

theorem body_closure_ci_function_body_progress_or_diverges_via_case_driver_body
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hentry
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body
      mkWhileReentry
      body_closure_ci_function_body_global_recursion
      hfrag hentry

/--
`BodyReadyCI` entry theorem is no longer a separate shell.
It is derived from the canonical closure-boundary theorem via `toClosureBoundary`.
-/
theorem body_ready_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  exact body_closure_ci_function_body_progress_or_diverges hfrag hready.toClosureBoundary

end Cpp
