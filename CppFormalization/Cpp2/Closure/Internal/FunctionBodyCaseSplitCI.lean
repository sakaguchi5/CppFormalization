import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Transitions.Minor.OpenScopeDecomposition
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseSplitCI

`body_*_function_body_progress_or_diverges_by_cases` を一枚板の shell のまま残さず、
statement 形ごとの honest な shell surface へ分解するための中間層。

設計意図:
- primitive は theorem-backed なので shell にしない。
- while は `WhileFunctionClosureKernelCI` 側へ切り出した。
- このファイルには、なお残る seq / ite / block の constructor shell だけを置く。
- `BodyReadyCI` は互換 wrapper として残し、canonical surface は
  `BodyClosureBoundaryCI` に寄せる。
-/

/-- canonical result shape for function-body closure statements. -/
abbrev FunctionBodyClosureResult (σ : State) (st : CppStmt) : Prop :=
  (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/--
Honest sequence shell.

必要なものを明示する:
- current entry boundary for the whole sequence
- left statement 自身の closure
- left normal 後の tail boundary reconstruction
- reconstructed tail boundary の下での tail closure
-/
axiom seq_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t)

/--
Honest if-shell.

必要なのは branch ごとの closure だけである。
condition evaluation と branch selection は `BodyClosureBoundaryCI` entry に含まれる
current-state readiness / adequacy から読む想定。
-/
axiom ite_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t))
    (thenClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyClosureBoundaryCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t)

/--
Honest block shell.

block 自体の closure を opened body 側へ還元する。
ここでは `OpenScope` で得られる opened-state boundary を明示前提にする。
-/
axiom block_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (openedClosure :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        BlockBodyClosureBoundaryCI Γ σ0 ss →
        FunctionBodyClosureResult σ0 (.block ss)) :
    FunctionBodyClosureResult σ (.block ss)

/-- `BodyReadyCI` 互換 wrapper for sequence. -/
theorem seq_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hleftBoundary => leftClosure hleftBoundary.toBodyReadyCI)
      (fun hty hstep => (tailBoundary hty hstep).toClosureBoundary)
      (fun hty hstep htailBoundary =>
        tailClosure hty hstep htailBoundary.toBodyReadyCI)

/-- `BodyReadyCI` 互換 wrapper for if. -/
theorem ite_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.ite c s t))
    (thenClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyReadyCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  exact
    ite_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hthenBoundary => thenClosure hthenBoundary.toBodyReadyCI)
      (fun helseBoundary => elseClosure helseBoundary.toBodyReadyCI)

/-- `BodyReadyCI` 互換 wrapper for block. -/
theorem block_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hentry : BodyReadyCI Γ σ (.block ss))
    (openedClosure :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        BlockBodyReadyCI Γ σ0 ss →
        FunctionBodyClosureResult σ0 (.block ss)) :
    FunctionBodyClosureResult σ (.block ss) := by
  exact
    block_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hopen hopenedBoundary =>
        openedClosure hopen hopenedBoundary.toBlockBodyReadyCI)

end Cpp
