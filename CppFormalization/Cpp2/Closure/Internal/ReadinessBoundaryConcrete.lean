import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtAbruptCompatibility
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.WhileNormalPreservation

namespace Cpp

/-!
# Closure.Internal.ReadinessBoundaryConcrete

`InternalClosureRoadmap` / `StateUpdateRoadmap` の readiness 境界公理を、
まず concrete 側で theorem 化する層。

ここで重要なのは `while` である。
full generic な residual readiness にはまだ full generic condition replay kernel が要るので、
現時点では
- generic typed theorem は従来どおり保持する
- さらに step 4/5 として replay-stable primitive body + replay-stable cond 版の
  theorem-backed corollary を追加する

という二段構成にする。
-/

theorem seq_left_normal_preserves_body_ready_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t := by
  intro htyLeft hreadySeq hstepLeft hσ
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hreadySeq
  have hσ' : ScopedTypedStateConcrete Δ σ' :=
    stmt_normal_preserves_scoped_typed_state_concrete
      htyLeft hσ hreadyLeft hstepLeft
  have hreadyRight : StmtReadyConcrete Δ σ' t :=
    seq_ready_right_after_left_normal htyLeft hσ' hreadySeq hstepLeft
  exact ⟨hσ', hreadyRight⟩

theorem block_head_normal_preserves_block_ready_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Δ →
    BlockReadyConcrete Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ BlockReadyConcrete Δ σ' ss := by
  intro htyHead hreadyBlock hstepHead hσ
  have hreadyHead : StmtReadyConcrete Γ σ s :=
    cons_block_ready_head hreadyBlock
  have hσ' : ScopedTypedStateConcrete Δ σ' :=
    stmt_normal_preserves_scoped_typed_state_concrete
      htyHead hσ hreadyHead hstepHead
  have hreadyTail : BlockReadyConcrete Δ σ' ss :=
    cons_block_ready_tail_after_head_normal htyHead hσ' hreadyBlock hstepHead
  exact ⟨hσ', hreadyTail⟩

/--
Typed concrete readiness boundary for the `body .normal` branch of `while`.

旧 signature では whole-while typing/readiness しか持っていなかったが、
新設計では residual readiness reconstruction は
`LoopBodyBoundaryCI` + `LoopReentryKernelCI` に委ねる。
-/
theorem while_body_normal_preserves_body_ready_concrete_typed
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ body .normal σ' →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hcond hbody K hstepBody
  have hN : HasTypeStmtCI .normalK Γ body Γ :=
    hbody.profile.normalTyping
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    stmt_normal_preserves_scoped_typed_state_concrete
      hN hbody.dynamic.state hbody.dynamic.safe hstepBody
  have hreadyTail : StmtReadyConcrete Γ σ' (.whileStmt c body) :=
    K.whileReady_after_normal hcond hbody hstepBody
  exact ⟨hσ', hreadyTail⟩

/--
Typed concrete readiness boundary for the `body .continueResult` branch of `while`.

continue branch も同様に、新設計では reentry kernel を明示的に要求する。
-/
theorem while_body_continue_preserves_body_ready_concrete_typed
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ body .continueResult σ' →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hcond hbody K hstepBody
  have hC : HasTypeStmtCI .continueK Γ body Γ :=
    hbody.profile.continueTyping
  have hcompBody : StmtControlCompatible hC hstepBody :=
    stmt_continue_control_compatible_of_normal
      stmt_normal_control_compatible hC hstepBody
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    stmt_continue_preserves_scoped_typed_state_concrete
      hC hstepBody hcompBody hbody.dynamic.state hbody.dynamic.safe
  have hreadyTail : StmtReadyConcrete Γ σ' (.whileStmt c body) :=
    K.whileReady_after_continue hcond hbody hstepBody
  exact ⟨hσ', hreadyTail⟩

/--
Step 4 の concrete corollary。
replay-stable primitive body かつ replay-stable cond では、condition replay kernel により
post-state の condition readiness を外から与えずに whole-while readiness を再構成できる。
-/
theorem while_body_normal_preserves_body_ready_concrete_typed_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hstable hcstable htyWhile hreadyWhile hstepBody hσ
  rcases while_normal_typing_data htyWhile with ⟨_, _, hN, _, _⟩
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hreadyWhile
  have hprim : PrimitiveNormalStmt body :=
    replay_stable_primitive_stmt_is_primitive_normal hstable
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim hN hσ hreadyBody hstepBody
  have hreadyTail : StmtReadyConcrete Γ σ' (.whileStmt c body) :=
    while_ready_after_body_normal_of_replay_stable_primitive
      hstable hcstable htyWhile hσ' hreadyWhile hstepBody
  exact ⟨hσ', hreadyTail⟩

/--
replay-stable primitive body には continue 分岐が無いので、
continue-case boundary は contradiction から閉じる。
-/
theorem while_body_continue_preserves_body_ready_concrete_typed_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hstable _ _ _ hstepBody _
  have hfalse : False := replay_stable_primitive_stmt_no_continue hstable hstepBody
  exact False.elim hfalse

end Cpp
