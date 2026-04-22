import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.LoopBodyFunctionClosureCI
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.WhileFunctionClosureKernelCI

Honest kernel surface for `while` function-body closure.

設計意図:
- `while` 全体の closure と、1 iteration の loop-body local closure を分離する。
- generic provider を theorem statement に埋め込まず、
  本当に必要な current-entry facts / tail-boundary reconstruction だけを
  surface に出す。
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
      BigStepStmt σ body .normal σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)
  afterContinue :
    ∀ {σ1 : State},
      BigStepStmt σ body .continueResult σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)

/--
Current-entry facts for one `while` iteration.

重要:
- ここには「今この state で current iteration を始めるための事実」だけを置く。
- body の local progress/divergence は `loopBoundary` から回復する。
- tail `while` の boundary 再構成は別の `WhileTailBoundaryKitCI` へ分離する。
-/
structure WhileCurrentEntryKitCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  typing :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ
  loopBoundary :
    LoopBodyBoundaryCI Γ σ body

namespace WhileCurrentEntryKitCI

/--
Local body progress/divergence is derived from the loop-body boundary itself.

current-entry kit はこの fact を field として重複保持しない。
-/
theorem bodyProgressOrDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (K : WhileCurrentEntryKitCI Γ σ c body) :
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body :=
  loop_body_function_progress_or_diverges_ci K.loopBoundary

end WhileCurrentEntryKitCI

/--
Current-entry support shell extracted from a top-level `while` closure boundary.

旧 `WhileEntrySupportCI` から、
- tail-boundary reconstruction
- local body progress/divergence
を切り離した版。
-/
axiom whileCurrentEntryKitCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileCurrentEntryKitCI Γ σ c body

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
