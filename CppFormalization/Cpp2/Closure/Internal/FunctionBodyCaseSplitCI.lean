import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseSplitCI

`body_*_function_body_progress_or_diverges_by_cases` を一枚板の shell のまま残さず、
statement 形ごとの honest な shell surface へ分解するための中間層。

設計意図:
- primitive は theorem-backed なので shell にしない。
- while は `WhileFunctionClosureKernelCI` 側へ切り出した。
- block は `BlockBodyClosureCI` 側へ切り出した。
- このファイルには、なお残る seq / ite の constructor shell だけを置く。
- `BodyReadyCI` は互換 wrapper として残し、canonical surface は
  `BodyClosureBoundaryCI` に寄せる。

更新:
- `seq` の tail-boundary については、post-state の dynamic 部分
  (`ScopedTypedStateConcrete` と `StmtReadyConcrete`) を theorem-backed にした。
- したがって残る shell は tail statement の structural / profile / adequacy を
  current `seq` entry からどう投影するか、という static 側だけである。
-/

/-- canonical result shape for function-body closure statements. -/
abbrev FunctionBodyClosureResult (σ : State) (st : CppStmt) : Prop :=
  (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/--
Non-dynamic part of a tail statement closure boundary after the left side of a sequence
has finished normally.

重要:
- `seq` の theorem-backed 部分は post-state `σ1` の dynamic 再構成である。
- それでも tail statement `t` の summary/profile/adequacy は自動では出ない。
- そこで、残る shell は非 dynamic 部分だけを bundle した scaffold に縮める。
-/
structure SeqTailClosureScaffoldCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ st
  profile : BodyControlProfile Γ st
  adequacy : BodyAdequacyCI Γ σ st profile

/--
Sequence tail non-dynamic scaffold after the left statement exits normally.

重要:
- 旧 `seq_tail_closure_boundary_ci_of_left_normal` は full boundary shell だった。
- いまは dynamic を theorem-backed にしたので、
  shell は structural / profile / adequacy の非 dynamic 部分だけでよい。
-/
axiom seq_tail_closure_scaffold_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      SeqTailClosureScaffoldCI Θ σ1 t

/--
Sequence tail-boundary reconstruction after the left statement exits normally.

これはもはや full shell ではない。
post-state の dynamic 部分は theorem-backed で再構成し、
残る非 dynamic scaffold だけを shell から受け取って assembled boundary を作る。
-/
noncomputable def seq_tail_closure_boundary_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      BodyClosureBoundaryCI Θ σ1 t := by
  intro Θ σ1 htyLeft hstepLeft
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      htyLeft hentry.dynamic.state hreadyLeft hstepLeft
  have hreadyRight : StmtReadyConcrete Θ σ1 t :=
    seq_ready_right_after_left_normal htyLeft hσ1 hentry.dynamic.safe hstepLeft
  let hs := seq_tail_closure_scaffold_ci_of_left_normal hentry htyLeft hstepLeft
  let hd : BodyDynamicBoundary Θ σ1 t :=
    { state := hσ1
      safe := hreadyRight }
  exact mkBodyClosureBoundaryCI hs.structural hs.profile hd hs.adequacy

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

end Cpp
