/- CppFormalization/Cpp2/Closure/Internal/WhileFunctionClosureKernelCI.lean -/
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.WhileEntryBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.LoopBodyFunctionClosureCI
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.WhileFunctionClosureKernelCI

Honest kernel surface for `while` function-body closure.

設計意図:
- `while` 全体の closure と、1 iteration の loop-body local closure を分離する。
- current-entry で読める事実は `WhileEntryBoundaryCI` から theorem-backed に読む。
- loop-body local boundary と tail-boundary reconstruction は、まだ別責務として残す。
- `LoopBodyBoundaryCI` / `LoopReentryKernelCI` は、この shell を後で
  theorem-backed に満たすための internal mechanism として使う。
-/

/--
Normal / continue の 1 iteration 後に、tail `while` の top-level closure boundary を
再構成するための kit.
-/
structure WhileTailBoundaryKitCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  afterNormal :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .normal σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)
  afterContinue :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .continueResult σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)

/--
Current-entry typing read directly from the theorem-backed `WhileEntryBoundaryCI`.

This is no longer a shell: the static-layer redesign makes the while header
typing data available from `BodyClosureBoundaryCI.static`.
-/
theorem whileTypingCI_of_whileEntryBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : WhileEntryBoundaryCI Γ σ c body) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ := by
  exact HasTypeStmtCI.while_normal hentry.hc hentry.hN hentry.hB hentry.hC

/--
Current-entry typing extracted from a top-level `while` closure boundary.

This is the first payoff of the `BodyStaticBoundaryCI` redesign:
the old axiom is now a theorem.
-/
theorem whileTypingCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ := by
  intro h
  exact whileTypingCI_of_whileEntryBoundaryCI
    (whileEntryBoundaryCI_of_bodyClosureBoundaryCI h)

/--
Current iteration の loop-body local boundary extracted from a top-level `while`
closure boundary.

This remains a real obligation.  The current entry gives only:
- condition typing/readiness,
- body normal/break/continue typing,
- current body readiness.

It does **not** by itself provide the 4-channel loop-body adequacy required by
`LoopBodyBoundaryCI`.
-/
axiom whileLoopBoundaryCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    LoopBodyBoundaryCI Γ σ body

/--
Local body progress/divergence extracted from a top-level `while` closure boundary.

これは独立な shell ではなく、loop-body boundary からの導出として置く。
-/
theorem whileBodyProgressOrDiverges_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body := by
  intro hentry
  exact
    loop_body_function_progress_or_diverges_ci
      (whileLoopBoundaryCI_of_bodyClosureBoundaryCI hentry)

/--
Tail-boundary reconstruction shell extracted from a top-level `while` closure boundary.

normal / continue の 1 iteration 後に、tail `while` へ渡す top-level closure
boundary を再構成する責務だけを分離する。
-/
axiom whileTailBoundaryKitCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileTailBoundaryKitCI Γ σ c body

/--
Honest while case theorem.

必要なものを明示する:
- current entry の top-level closure boundary
- current iteration の loop-body local boundary
- current iteration 自身の local progress/divergence
- normal / continue 後の tail-boundary reconstruction
- tail `while` そのものの recursive closure hypothesis
-/
axiom while_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body)
    (hbodyClosure :
      (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body)
    (htailBoundary : WhileTailBoundaryKitCI Γ σ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body)

end Cpp
