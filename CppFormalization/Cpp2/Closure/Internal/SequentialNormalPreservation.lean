import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.ReadinessResidualBoundary
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
`seq` について最初に必要なのは、全体 preservation ではなく、
左が `.normal` で終わったあとに右側へ渡る境界の再構成である。

このファイルでは
- `HasTypeStmtCI .normalK Γ (.seq s t) Δ` の分解
- `StmtReadyConcrete Γ σ (.seq s t)` から左 ready を取り出すこと
- 左が normal 実行されたあと、右側の ready を再構成すること
を整理する。

注意:
- `seq_typing_data` と `seq_ready_left` は純粋な inversion なので theorem 化した。
- `seq_ready_right_after_left_normal` は見た目は decomposition だが、
  実際には residual readiness / replay の核であり、まだ honest に lower replay
  kernel を要求する段階にある。
-/


/- =========================================================
   1. seq の typing / readiness 分解
   ========================================================= -/

theorem seq_typing_data
    {Γ Δ : TypeEnv} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ ->
    ∃ Θ,
      HasTypeStmtCI .normalK Γ s Θ ∧
      HasTypeStmtCI .normalK Θ t Δ := by
  intro h
  cases h with
  | seq_normal hs ht =>
      exact ⟨_, hs, ht⟩

theorem seq_ready_left
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.seq s t) ->
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | seq hs _ =>
      exact hs

axiom seq_ready_right_after_left_normal
    {Γ Θ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Θ ->
    ScopedTypedStateConcrete Θ σ' ->
    StmtReadyConcrete Γ σ (.seq s t) ->
    BigStepStmt σ s .normal σ' ->
    StmtReadyConcrete Θ σ' t


/- =========================================================
   2. residual boundary の抽出
   ========================================================= -/

theorem primitive_left_seq_normal_preserves_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    (match s with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) ->
    HasTypeStmtCI .normalK Γ (.seq s t) Δ ->
    ScopedTypedStateConcrete Γ σ ->
    StmtReadyConcrete Γ σ (.seq s t) ->
    BigStepStmt σ s .normal σ' ->
    SeqResidualBoundary Δ σ' t := by
  intro hprim htySeq hσ hreadySeq hstepLeft
  rcases seq_typing_data htySeq with ⟨Θ, htyLeft, htyRight⟩
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hreadySeq
  have hσ' : ScopedTypedStateConcrete Θ σ' :=
    primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim htyLeft hσ hreadyLeft hstepLeft
  have hreadyRight : StmtReadyConcrete Θ σ' t :=
    seq_ready_right_after_left_normal htyLeft hσ' hreadySeq hstepLeft
  exact ⟨Θ, htyRight, hσ', hreadyRight⟩

theorem primitive_left_seq_normal_preserves_right_state
    {Γ Δ Θ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    (match s with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) ->
    HasTypeStmtCI .normalK Γ (.seq s t) Δ ->
    ScopedTypedStateConcrete Γ σ ->
    StmtReadyConcrete Γ σ (.seq s t) ->
    BigStepStmt σ s .normal σ' ->
    HasTypeStmtCI .normalK Θ t Δ ->
    (∀ {Θ'}, HasTypeStmtCI .normalK Θ' t Δ -> Θ' = Θ) ->
    ScopedTypedStateConcrete Θ σ' := by
  intro hprim htySeq hσ hreadySeq hstepLeft htyRight huniq
  rcases primitive_left_seq_normal_preserves_residual_boundary
      hprim htySeq hσ hreadySeq hstepLeft with
    ⟨Θ', htyRight', hσ', hreadyRight'⟩
  have hEq : Θ' = Θ := by
    exact huniq htyRight'
  subst hEq
  exact hσ'

theorem primitive_left_seq_normal_preserves_right_ready
    {Γ Δ Θ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    (match s with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) ->
    HasTypeStmtCI .normalK Γ (.seq s t) Δ ->
    ScopedTypedStateConcrete Γ σ ->
    StmtReadyConcrete Γ σ (.seq s t) ->
    BigStepStmt σ s .normal σ' ->
    HasTypeStmtCI .normalK Θ t Δ ->
    (∀ {Θ'}, HasTypeStmtCI .normalK Θ' t Δ -> Θ' = Θ) ->
    StmtReadyConcrete Θ σ' t := by
  intro hprim htySeq hσ hreadySeq hstepLeft htyRight huniq
  rcases primitive_left_seq_normal_preserves_residual_boundary
      hprim htySeq hσ hreadySeq hstepLeft with
    ⟨Θ', htyRight', hσ', hreadyRight'⟩
  have hEq : Θ' = Θ := by
    exact huniq htyRight'
  subst hEq
  exact hreadyRight'

end Cpp
