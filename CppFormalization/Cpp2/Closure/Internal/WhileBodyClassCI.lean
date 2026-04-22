import CppFormalization.Cpp2.Closure.Internal.WhileFunctionClosureKernelCI

namespace Cpp

/-!
# Closure.Internal.WhileBodyClassCI

`while` を theorem-backed にできる body class を明示するための internal vocabulary.

狙い:
- これまで `while` の honest kernel は
  * loop-body boundary
  * local progress/divergence
  * tail-boundary reconstruction
  をばらばらに受け取っていた。
- しかし数学的にも C++ 的にも、ここは「どの kinds of body なら while を閉じられるか」
  という semantic class の問題である。
- そこで、`while` current entry で必要な body-local support を
  一つの class object として固定する。
-/

structure WhileBodyClassCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  loopBoundary :
    LoopBodyBoundaryCI Γ σ body
  tailBoundary :
    WhileTailBoundaryKitCI Γ σ c body

namespace WhileBodyClassCI

/--
Local body progress/divergence is derived from the class boundary itself.
-/
theorem bodyProgressOrDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (K : WhileBodyClassCI Γ σ c body) :
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body :=
  loop_body_function_progress_or_diverges_ci K.loopBoundary

end WhileBodyClassCI

/--
Class shell extracted from a top-level `while` closure boundary.

`while` case-driver の mainline は current-entry の local boundary と
tail-boundary reconstruction を別々に直接触る代わりに、
この class object を経由して while-local debt をまとめて扱う。
-/
axiom whileBodyClassCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileBodyClassCI Γ σ c body

/--
Class-based wrapper around the honest while kernel.

これにより、while の caller は
「body class がある」
という一つの事実だけを供給すればよくなる。
-/
theorem while_function_body_closure_boundary_ci_of_class
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (K : WhileBodyClassCI Γ σ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_honest
      htyWhile
      hentry
      K.loopBoundary
      K.bodyProgressOrDiverges
      K.tailBoundary
      htailClosure

end Cpp
