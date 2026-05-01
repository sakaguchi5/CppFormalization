
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtAbruptCompatibility
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReplayStablePrimitiveFacts

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
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ StmtReadyConcrete Δ σ' t := by
  intro htyLeft hreadySeq hstepLeft hσ
  exact
    seq_left_normal_preserves_ready_of_left_preservation
      (Γ := Γ) (Δ := Δ) (σ := σ) (σ' := σ') (s := s) (t := t)
      (hpres := by
        intro htyLeft' hσ0 hreadyLeft0 hstepLeft0
        exact
          stmt_normal_preserves_scoped_typed_state_concrete
            mkWhileReentry htyLeft' hσ0 hreadyLeft0 hstepLeft0)
      htyLeft hreadySeq hstepLeft hσ

theorem block_head_normal_preserves_block_ready_concrete
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Δ →
    BlockReadyConcrete Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' ∧ BlockReadyConcrete Δ σ' ss := by
  intro htyHead hreadyBlock hstepHead hσ
  exact
    cons_head_normal_preserves_ready_of_head_preservation
      (Γ := Γ) (Ξ := Δ) (σ := σ) (σ' := σ') (s := s) (ss := ss)
      (hpres := by
        intro htyHead' hσ0 hreadyHead0 hstepHead0
        exact
          stmt_normal_preserves_scoped_typed_state_concrete
            mkWhileReentry htyHead' hσ0 hreadyHead0 hstepHead0)
      htyHead hreadyBlock hstepHead hσ

theorem while_body_normal_preserves_entry_ready_concrete_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ body .normal σ' →
    ScopedTypedStateConcrete Γ σ' ∧ WhileEntryReadyCI Γ σ' c body := by
  intro hcond hbody K hstepBody
  have hN : HasTypeStmtCI .normalK Γ body Γ :=
    hbody.profile.normalTyping
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    stmt_normal_preserves_scoped_typed_state_concrete
      mkWhileReentry
      hN hbody.dynamic.state hbody.dynamic.safe hstepBody
  have hentry' : WhileEntryReadyCI Γ σ' c body :=
    whileEntryReady_after_normal_of_loopReentry hcond hbody K hstepBody
  exact ⟨hσ', hentry'⟩

theorem while_body_continue_preserves_entry_ready_concrete_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ body .continueResult σ' →
    ScopedTypedStateConcrete Γ σ' ∧ WhileEntryReadyCI Γ σ' c body := by
  intro hcond hbody K hstepBody
  have hC : HasTypeStmtCI .continueK Γ body Γ :=
    hbody.profile.continueTyping
  have hcompBody : StmtControlCompatible hC hstepBody :=
    stmt_continue_control_compatible_of_normal
      stmt_normal_control_compatible hC hstepBody
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    stmt_continue_preserves_scoped_typed_state_concrete
      mkWhileReentry
      hC hstepBody hcompBody hbody.dynamic.state hbody.dynamic.safe
  have hentry' : WhileEntryReadyCI Γ σ' c body :=
    whileEntryReady_after_continue_of_loopReentry hcond hbody K hstepBody
  exact ⟨hσ', hentry'⟩


theorem while_body_normal_preserves_body_ready_concrete_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ body .normal σ' →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hcond hbody K hstepBody
  rcases while_body_normal_preserves_entry_ready_concrete_typed
      mkWhileReentry hcond hbody K hstepBody with
    ⟨hσ', hentry'⟩
  exact ⟨hσ', stmtReady_of_whileEntryReady K.hc hentry'⟩

theorem while_body_continue_preserves_body_ready_concrete_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ body .continueResult σ' →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hcond hbody K hstepBody
  rcases while_body_continue_preserves_entry_ready_concrete_typed
      mkWhileReentry hcond hbody K hstepBody with
    ⟨hσ', hentry'⟩
  exact ⟨hσ', stmtReady_of_whileEntryReady K.hc hentry'⟩

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
  rcases while_typing_data htyWhile with ⟨_, _, hN, _, _⟩
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hreadyWhile
  have hprim := replay_stable_primitive_stmt_is_primitive_normal hstable
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
