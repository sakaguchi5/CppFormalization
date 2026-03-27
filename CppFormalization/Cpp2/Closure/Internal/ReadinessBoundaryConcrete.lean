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
現行の concrete API では residual readiness の再構成補題
`while_ready_after_body_normal` / `while_ready_after_body_continue`
が body の CI normal typing を要求する。
したがって roadmap に書かれている「typing 仮定なし while readiness 境界」は、
今の concrete interface からはそのままは出ない。

なのでこのファイルでは:
- `seq` / `block` は roadmap と同型の concrete theorem をそのまま置く
- `while` は honest に whole-while typing を仮定した typed 版を置く
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

This is the strongest theorem honestly derivable from the current concrete interface.
The weaker signature without `htyWhile` is not available yet.
-/
theorem while_body_normal_preserves_body_ready_concrete_typed
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro htyWhile hreadyWhile hstepBody hσ
  rcases while_normal_typing_data htyWhile with ⟨_, hN, hB, hC⟩
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hreadyWhile
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    stmt_normal_preserves_scoped_typed_state_concrete
      hN hσ hreadyBody hstepBody
  have hreadyTail : StmtReadyConcrete Γ σ' (.whileStmt c body) :=
    while_ready_after_body_normal hN hσ' hreadyWhile hstepBody
  exact ⟨hσ', hreadyTail⟩

/--
Typed concrete readiness boundary for the `body .continueResult` branch of `while`.

Again, the whole-while normal typing is the honest hypothesis: from it we recover both the
body normal typing needed for readiness reconstruction and the body continue typing needed for
continue-path compatibility.
-/
theorem while_body_continue_preserves_body_ready_concrete_typed
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Γ σ' ∧ StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro htyWhile hreadyWhile hstepBody hσ
  rcases while_normal_typing_data htyWhile with ⟨_, hN, hB, hC⟩
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hreadyWhile
  have hcompBody : StmtControlCompatible hC hstepBody :=
    stmt_continue_control_compatible_of_normal stmt_normal_control_compatible hC hstepBody
  have hσ' : ScopedTypedStateConcrete Γ σ' :=
    stmt_continue_preserves_scoped_typed_state_concrete hC hstepBody hcompBody hσ hreadyBody
  have hreadyTail : StmtReadyConcrete Γ σ' (.whileStmt c body) :=
    while_ready_after_body_continue hN hσ' hreadyWhile hstepBody
  exact ⟨hσ', hreadyTail⟩

end Cpp
