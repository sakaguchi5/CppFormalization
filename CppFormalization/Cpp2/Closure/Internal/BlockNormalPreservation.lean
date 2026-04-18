
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Transitions.Minor.OpenScopeDecomposition
import CppFormalization.Cpp2.Closure.Transitions.Major.CloseScopeTopFrameExtension

namespace Cpp

/-!
`block` の normal-path preservation。

本質は次の三段階:
1. block 入口で `OpenScope`
2. 開いた scope の中で `BigStepBlock ... .normal`
3. body 後の拡張 top frame を `CloseScope` で消して outer Γ に戻す

ここで重要なのは、body の normal 実行後の型環境は
単なる `pushTypeScope Γ` ではなく、その top frame に局所宣言が追加された
ある `Θ` になりうること。
したがって close には
「Θ が Γ の block 内 top-frame extension なら、close で Γ に戻る」
という一般化原理が必要になる。
-/

/- =========================================================
   1. block 内部環境の抽象化
   ========================================================= -/

def BlockBodyPreservesWithinOpenScope
    (Γ : TypeEnv) (ss : StmtBlock) : Prop :=
  ∀ {Θ : TypeEnv} {σ0 σ1 : State},
    TopFrameExtensionOf Γ Θ →
    HasTypeBlockCI .normalK (pushTypeScope Γ) ss Θ →
    ScopedTypedStateConcrete (pushTypeScope Γ) σ0 →
    BlockReadyConcrete (pushTypeScope Γ) σ0 ss →
    BigStepBlock σ0 ss .normal σ1 →
    ScopedTypedStateConcrete Θ σ1


/- =========================================================
   2. typing / readiness / operational 分解
   ========================================================= -/

axiom block_typing_data
    {Γ Δ : TypeEnv} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ (.block ss) Δ →
    Δ = Γ ∧ ∃ Θ,
      TopFrameExtensionOf Γ Θ ∧
      HasTypeBlockCI .normalK (pushTypeScope Γ) ss Θ

axiom block_ready_opened_body
    {Γ : TypeEnv} {σ σ0 : State} {ss : StmtBlock} :
    StmtReadyConcrete Γ σ (.block ss) →
    OpenScope σ σ0 →
    BlockReadyConcrete (pushTypeScope Γ) σ0 ss

axiom block_normal_data
    {σ σ' : State} {ss : StmtBlock} :
    BigStepStmt σ (.block ss) .normal σ' →
    ∃ σ0 σ1,
      OpenScope σ σ0 ∧
      BigStepBlock σ0 ss .normal σ1 ∧
      CloseScope σ1 σ'

/- =========================================================
   3. generic theorem
   ========================================================= -/

theorem block_normal_preserves_scoped_typed_state_from_body
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ (.block ss) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.block ss) →
    BigStepStmt σ (.block ss) .normal σ' →
    BlockBodyPreservesWithinOpenScope Γ ss →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep hbody
  rcases block_typing_data hty with ⟨hΔ, Θ, hExt, hbodyTy⟩
  rcases block_normal_data hstep with ⟨σ0, σ1, hopen, hbodyStep, hclose⟩
  have hσ0 : ScopedTypedStateConcrete (pushTypeScope Γ) σ0 :=
    openScope_preserves_scoped_typed_state_concrete hσ hopen
  have hready0 : BlockReadyConcrete (pushTypeScope Γ) σ0 ss :=
    block_ready_opened_body hready hopen
  have hσ1 : ScopedTypedStateConcrete Θ σ1 :=
    hbody hExt hbodyTy hσ0 hready0 hbodyStep
  subst hΔ
  exact closeScope_preserves_outer_from_topFrameExtension hExt hσ1 hclose

theorem block_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ (.block ss) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.block ss) →
    BigStepStmt σ (.block ss) .normal σ' →
    BlockBodyPreservesWithinOpenScope Γ ss →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep hbody
  exact block_normal_preserves_scoped_typed_state_from_body
    hty hσ hready hstep hbody

end Cpp
