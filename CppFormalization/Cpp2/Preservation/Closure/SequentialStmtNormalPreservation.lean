import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Static.Typing.ControlIndexed
import CppFormalization.Cpp2.Preservation.Closure.SequentialNormalPreservation

namespace Cpp

/-!
`seq` 全体の normal-path preservation。

既にある `SequentialNormalPreservation.lean` では、
左が `.normal` で終わったあとに右へ渡す境界
(`ScopedTypedStateConcrete` と `StmtReadyConcrete`) を再構成する補題群を置いてある。

このファイルではそこに
- `BigStepStmt σ (.seq s t) .normal σ'` の operational 分解
- 左右の subproof から全体 preservation を組み立てる theorem
を追加する。
-/

/- =========================================================
   1. operational 分解
   ========================================================= -/

theorem seq_normal_data
    {σ σ' : State} {s t : CppStmt} :
    BigStepStmt σ (.seq s t) .normal σ' →
    ∃ σ1,
      BigStepStmt σ s .normal σ1 ∧
      BigStepStmt σ1 t .normal σ' := by
  intro h
  cases h with
  | seqNormal hs ht =>
      exact ⟨_, hs, ht⟩

/- =========================================================
   2. 左右の subproof から全体 preservation を組み立てる
   ========================================================= -/

theorem seq_normal_preserves_scoped_typed_state_from_subproofs
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ (.seq s t) .normal σ' →
    (∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ1 →
      ScopedTypedStateConcrete Θ σ1) →
    (∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Θ t Δ →
      ScopedTypedStateConcrete Θ σ1 →
      StmtReadyConcrete Θ σ1 t →
      BigStepStmt σ1 t .normal σ' →
      ScopedTypedStateConcrete Δ σ') →
    (∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      ScopedTypedStateConcrete Θ σ1 →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ1 →
      StmtContinuationDynamicBoundary Θ σ1 t) →
    ScopedTypedStateConcrete Δ σ' := by
  intro htySeq hσ hreadySeq hstepSeq hleft hright htail
  rcases seq_typing_data htySeq with ⟨Θ, htyLeft, htyRight⟩
  rcases seq_normal_data hstepSeq with ⟨σ1, hleftStep, hrightStep⟩

  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hreadySeq

  have hσ1 : ScopedTypedStateConcrete Θ σ1 :=
    hleft htyLeft hreadyLeft hleftStep

  have htailDyn : StmtContinuationDynamicBoundary Θ σ1 t :=
    htail htyLeft hσ1 hreadySeq hleftStep

  exact hright htyRight htailDyn.state htailDyn.safe hrightStep

/- =========================================================
   3. statement 全体の normal preservation を仮定した簡約版
   `stmt_normal_preserves_scoped_typed_state_concrete` の seq case から
   呼ぶための theorem。
   ========================================================= -/

theorem seq_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ (.seq s t) .normal σ' →
    (∀ {Γ' Δ' : TypeEnv} {σ0 σ1 : State} {u : CppStmt},
      HasTypeStmtCI .normalK Γ' u Δ' →
      ScopedTypedStateConcrete Γ' σ0 →
      StmtReadyConcrete Γ' σ0 u →
      BigStepStmt σ0 u .normal σ1 →
      ScopedTypedStateConcrete Δ' σ1) →
    (∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      ScopedTypedStateConcrete Θ σ1 →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ1 →
      StmtContinuationDynamicBoundary Θ σ1 t) →
    ScopedTypedStateConcrete Δ σ' := by
  intro htySeq hσ hreadySeq hstepSeq hstmt htail
  refine
    seq_normal_preserves_scoped_typed_state_from_subproofs
      htySeq hσ hreadySeq hstepSeq ?_ ?_ ?_

  · intro Θ σ1 htyLeft hreadyLeft hleftStep
    exact hstmt htyLeft hσ hreadyLeft hleftStep

  · intro Θ σ1 htyRight hσ1 hreadyRight hrightStep
    exact hstmt htyRight hσ1 hreadyRight hrightStep

  · intro Θ σ1 htyLeft hσ1 hreadySeq' hleftStep
    exact htail htyLeft hσ1 hreadySeq' hleftStep

end Cpp
