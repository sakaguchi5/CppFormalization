/- CppFormalization/Cpp2/Closure/Internal/WhileFunctionClosureKernelCI.lean -/
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
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .normal σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)
  afterContinue :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .continueResult σ1 →
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body)

/--
Current-entry typing extracted from a top-level `while` closure boundary.

debt を個別の slot に露出するための細い shell.
-/
axiom whileTypingCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ

/--
Current iteration の loop-body local boundary extracted from a top-level `while`
closure boundary.

current-entry の local boundary を bundle ではなく個別に扱う。
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
