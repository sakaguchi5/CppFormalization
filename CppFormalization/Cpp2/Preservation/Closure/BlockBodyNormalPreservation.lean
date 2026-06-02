import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Static.Typing.ControlIndexed
import CppFormalization.Cpp2.Metatheory.Closure.Unclassified.ReadinessResidualBoundary
import CppFormalization.Cpp2.Continuation.Boundary.Cons

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

重要:
- low-level exact block-tail ready kernel / `削除済みaxiom`
  にはもう給電しない。
- current mainline が public に使うべき主語は `BlockReadyConcrete Ξ σ' ss`
  単体ではなく、post-route の `BlockContinuationDynamicBoundary Ξ σ' ss`、
  あるいはそれを詰めた `ConsResidualBoundary Θ σ' ss` である。
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

/--
Low-level block-tail ready projection from an explicit tail continuation
boundary.

This is no longer a transport theorem.  Tail readiness is obtained by projecting
from the post-route continuation boundary.
-/
theorem cons_block_ready_tail_after_head_normal_of_tail_continuation
    {Ξ : TypeEnv} {σ' : State} {ss : StmtBlock}
    (tail : BlockContinuationDynamicBoundary Ξ σ' ss) :
    BlockReadyConcrete Ξ σ' ss :=
  tail.safe

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

/- =========================================================
   2. head-normal post boundary の一般定理
   ========================================================= -/

/--
When the post-environment of the head statement is already fixed as `Ξ`,
we can reconstruct the concrete state/ready pair for the remaining block tail
without mentioning the final codomain of the whole block body.

The block-tail readiness is projected from an explicit post-route block-tail
continuation boundary.
-/
theorem cons_head_normal_preserves_ready_of_head_preservation
    {Γ Ξ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (hpres :
      HasTypeStmtCI .normalK Γ s Ξ ->
      ScopedTypedStateConcrete Γ σ ->
      StmtReadyConcrete Γ σ s ->
      BigStepStmt σ s .normal σ' ->
      ScopedTypedStateConcrete Ξ σ')
    (htail :
      HasTypeStmtCI .normalK Γ s Ξ ->
      ScopedTypedStateConcrete Ξ σ' ->
      BlockReadyConcrete Γ σ (.cons s ss) ->
      BigStepStmt σ s .normal σ' ->
      BlockContinuationDynamicBoundary Ξ σ' ss) :
    HasTypeStmtCI .normalK Γ s Ξ ->
    BlockReadyConcrete Γ σ (.cons s ss) ->
    BigStepStmt σ s .normal σ' ->
    ScopedTypedStateConcrete Γ σ ->
    ScopedTypedStateConcrete Ξ σ' ∧ BlockReadyConcrete Ξ σ' ss := by
  intro htyHead hready hstep hσ
  have hreadyHead : StmtReadyConcrete Γ σ s :=
    cons_block_ready_head hready
  have hσ' : ScopedTypedStateConcrete Ξ σ' :=
    hpres htyHead hσ hreadyHead hstep
  have htailDyn : BlockContinuationDynamicBoundary Ξ σ' ss :=
    htail htyHead hσ' hready hstep
  exact ⟨htailDyn.state, htailDyn.safe⟩

/--
Generic cons residual-boundary reconstruction after a head normal step.

The two abstract inputs are separated:

* `hhead` proves the post-state invariant for the intermediate environment `Ξ`;
* `htail` proves that the selected post-route block-tail continuation exists.

Thus the theorem no longer manufactures tail readiness by exact-tail transport.
-/
theorem cons_head_normal_preserves_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (hty : HasTypeBlockCI .normalK Γ (.cons s ss) Θ)
    (hσ : ScopedTypedStateConcrete Γ σ)
    (hready : BlockReadyConcrete Γ σ (.cons s ss))
    (hstep : BigStepStmt σ s .normal σ')
    (hhead :
      ∀ {Ξ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Ξ ->
        ScopedTypedStateConcrete Γ σ ->
        StmtReadyConcrete Γ σ s ->
        BigStepStmt σ s .normal σ1 ->
        ScopedTypedStateConcrete Ξ σ1)
    (htail :
      ∀ {Ξ : TypeEnv},
        HasTypeStmtCI .normalK Γ s Ξ ->
        HasTypeBlockCI .normalK Ξ ss Θ ->
        ScopedTypedStateConcrete Ξ σ' ->
        BlockReadyConcrete Γ σ (.cons s ss) ->
        BigStepStmt σ s .normal σ' ->
        BlockContinuationDynamicBoundary Ξ σ' ss) :
    ConsResidualBoundary Θ σ' ss := by
  rcases cons_block_typing_data hty with ⟨Ξ, htyHead, htyTail⟩
  have hreadyHead : StmtReadyConcrete Γ σ s :=
    cons_block_ready_head hready
  have hσ' : ScopedTypedStateConcrete Ξ σ' :=
    hhead htyHead hσ hreadyHead hstep
  have htailDyn : BlockContinuationDynamicBoundary Ξ σ' ss :=
    htail htyHead htyTail hσ' hready hstep
  exact ⟨Ξ, htyTail, htailDyn.state, htailDyn.safe⟩


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
    (∀ {Ξ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Ξ ->
      HasTypeBlockCI .normalK Ξ ss Θ ->
      ScopedTypedStateConcrete Ξ σ1 ->
      BlockReadyConcrete Γ σ (.cons s ss) ->
      BigStepStmt σ s .normal σ1 ->
      BlockContinuationDynamicBoundary Ξ σ1 ss) ->
    (∀ {Ξ : TypeEnv} {σ1 σ2 : State},
      HasTypeBlockCI .normalK Ξ ss Θ ->
      ScopedTypedStateConcrete Ξ σ1 ->
      BlockReadyConcrete Ξ σ1 ss ->
      BigStepBlock σ1 ss .normal σ2 ->
      ScopedTypedStateConcrete Θ σ2) ->
    ScopedTypedStateConcrete Θ σ' := by
  intro hty hσ hready hstep hhead htailCont htail
  rcases cons_block_normal_data hstep with ⟨σ1, hheadStep, htailStep⟩
  rcases cons_head_normal_preserves_residual_boundary
      hty hσ hready hheadStep hhead htailCont with
    ⟨Ξ, htyTail, hσ1, hreadyTail⟩
  exact htail htyTail hσ1 hreadyTail htailStep

end Cpp
