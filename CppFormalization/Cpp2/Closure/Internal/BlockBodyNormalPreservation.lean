
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.ReadinessResidualBoundary

namespace Cpp

/-!
`StmtBlock` の normal-path preservation。

ここでは block body を
- empty block
- head :: tail
に分解して扱う。

本質は `cons` のとき、
head が `.normal` で終わったあとに
tail へ渡す境界を再構成できること。
そのために block-level の typing / readiness / operational 分解を置く。
-/


/- =========================================================
   1. block typing / readiness / operational data
   ========================================================= -/

theorem empty_block_typing_data
    {Γ Θ : TypeEnv} :
    HasTypeBlockCI .normalK Γ .nil Θ ->
    Θ = Γ := by
  intro h
  cases h
  rfl

theorem empty_block_ready_trivial
    {Γ : TypeEnv} {σ : State} :
    BlockReadyConcrete Γ σ .nil :=
  BlockReadyConcrete.nil

theorem empty_block_normal_data
    {σ σ' : State} :
    BigStepBlock σ .nil .normal σ' ->
    σ' = σ := by
  intro h
  cases h
  rfl

theorem cons_block_typing_data
    {Γ Θ : TypeEnv} {s : CppStmt} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ (.cons s ss) Θ ->
    ∃ Ξ,
      HasTypeStmtCI .normalK Γ s Ξ ∧
      HasTypeBlockCI .normalK Ξ ss Θ := by
  intro h
  cases h with
  | cons_normal hs hss =>
      exact ⟨_, hs, hss⟩

theorem cons_block_ready_head
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ (.cons s ss) ->
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | cons hs _ =>
      exact hs

axiom cons_block_ready_tail_after_head_normal
    {Γ Ξ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Ξ ->
    ScopedTypedStateConcrete Ξ σ' ->
    BlockReadyConcrete Γ σ (.cons s ss) ->
    BigStepStmt σ s .normal σ' ->
    BlockReadyConcrete Ξ σ' ss

theorem cons_block_normal_data
    {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    BigStepBlock σ (.cons s ss) .normal σ' ->
    ∃ σ1,
      BigStepStmt σ s .normal σ1 ∧
      BigStepBlock σ1 ss .normal σ' := by
  intro h
  cases h with
  | consNormal hs hss =>
      exact ⟨_, hs, hss⟩

theorem cons_head_normal_preserves_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ (.cons s ss) Θ ->
    ScopedTypedStateConcrete Γ σ ->
    BlockReadyConcrete Γ σ (.cons s ss) ->
    BigStepStmt σ s .normal σ' ->
    (∀ {Ξ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Ξ ->
      ScopedTypedStateConcrete Γ σ ->
      StmtReadyConcrete Γ σ s ->
      BigStepStmt σ s .normal σ1 ->
      ScopedTypedStateConcrete Ξ σ1) ->
    ConsResidualBoundary Θ σ' ss := by
  intro hty hσ hready hstep hhead
  rcases cons_block_typing_data hty with ⟨Ξ, htyHead, htyTail⟩
  have hreadyHead : StmtReadyConcrete Γ σ s :=
    cons_block_ready_head hready
  have hσ' : ScopedTypedStateConcrete Ξ σ' :=
    hhead htyHead hσ hreadyHead hstep
  have hreadyTail : BlockReadyConcrete Ξ σ' ss :=
    cons_block_ready_tail_after_head_normal htyHead hσ' hready hstep
  exact ⟨Ξ, htyTail, hσ', hreadyTail⟩


/- =========================================================
   3. block body の normal preservation
   ========================================================= -/

theorem empty_block_normal_preserves_scoped_typed_state_concrete
    {Γ Θ : TypeEnv} {σ σ' : State} :
    HasTypeBlockCI .normalK Γ .nil Θ ->
    ScopedTypedStateConcrete Γ σ ->
    BlockReadyConcrete Γ σ .nil ->
    BigStepBlock σ .nil .normal σ' ->
    ScopedTypedStateConcrete Θ σ' := by
  intro hty hσ hready hstep
  rcases empty_block_typing_data hty with hΘ
  rcases empty_block_normal_data hstep with hEq
  subst hΘ
  subst hEq
  exact hσ

theorem cons_block_normal_preserves_scoped_typed_state_from_head_and_tail
    {Γ Θ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeBlockCI .normalK Γ (.cons s ss) Θ ->
    ScopedTypedStateConcrete Γ σ ->
    BlockReadyConcrete Γ σ (.cons s ss) ->
    BigStepBlock σ (.cons s ss) .normal σ' ->
    (∀ {Ξ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Ξ ->
      ScopedTypedStateConcrete Γ σ ->
      StmtReadyConcrete Γ σ s ->
      BigStepStmt σ s .normal σ1 ->
      ScopedTypedStateConcrete Ξ σ1) ->
    (∀ {Ξ : TypeEnv} {σ1 σ2 : State},
      HasTypeBlockCI .normalK Ξ ss Θ ->
      ScopedTypedStateConcrete Ξ σ1 ->
      BlockReadyConcrete Ξ σ1 ss ->
      BigStepBlock σ1 ss .normal σ2 ->
      ScopedTypedStateConcrete Θ σ2) ->
    ScopedTypedStateConcrete Θ σ' := by
  intro hty hσ hready hstep hhead htail
  rcases cons_block_normal_data hstep with ⟨σ1, hheadStep, htailStep⟩
  rcases cons_head_normal_preserves_residual_boundary
      hty hσ hready hheadStep hhead with
    ⟨Ξ, htyTail, hσ1, hreadyTail⟩
  exact htail htyTail hσ1 hreadyTail htailStep

end Cpp
