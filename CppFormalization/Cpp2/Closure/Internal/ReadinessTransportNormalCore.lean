import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormal

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalCore

`ReadinessTransportNormal.lean` で固定した transport context / goal aliases の上に、
将来の mutual ready-transport theorem family を一箇所へ束ねる core file。

この段階ではまだ theorem-backed 実装は入れない。
代わりに、

- place / expr / stmt / block の4本の future core goals
- 現在の mainline がまだ直接使っている legacy exact kernels
  (`seq_ready_right_after_left_normal`,
   `cons_block_ready_tail_after_head_normal`)

を一つの bundled kernel にまとめる。

重要:
- これは「axiom を増やす」ためのファイルではない。
  既存の局所 debt を、将来 theorem に差し替えるための single choke point
  に集約するための file である。
- いま上位層は `SequentialNormalPreservation` / `BlockBodyNormalPreservation`
  の中間 theorem を経由する形へかなり下がっている。
  次段階では、そこに残る exact tail-ready kernels をこの core から給電し、
  さらにその後 core 自体を theorem-backed に置き換える。
-/


/- =========================================================
   1. bundled future kernel surface
   ========================================================= -/

structure ReadinessTransportNormalCore : Type where
  placeTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      PlaceReadyTransportGoal Γ Δ σ σ' head

  exprTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      ExprReadyTransportGoal Γ Δ σ σ' head

  stmtTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      StmtReadyTransportGoal Γ Δ σ σ' head

  blockTransport :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt},
      BlockReadyTransportGoal Γ Δ σ σ' head

  /--
  Legacy exact seq tail kernel still consumed by current mainline.

  Long-term target:
  this should become a corollary of `stmtTransport` once the mutual transport
  family is theorem-backed strongly enough.
  -/
  seqRightAfterLeftNormal :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt},
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Δ σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtReadyConcrete Δ σ' t

  /--
  Legacy exact block-tail kernel still consumed by current mainline.

  Long-term target:
  this should become a corollary of `blockTransport` once the mutual transport
  family is theorem-backed strongly enough.
  -/
  consTailAfterHeadNormal :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock},
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Δ σ' →
      BlockReadyConcrete Γ σ (.cons s ss) →
      BigStepStmt σ s .normal σ' →
      BlockReadyConcrete Δ σ' ss


/- =========================================================
   2. current bundled kernel
   ========================================================= -/

axiom readinessTransportNormalCore : ReadinessTransportNormalCore


/- =========================================================
   3. thin projection theorems
   ========================================================= -/

theorem place_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    PlaceReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.placeTransport

theorem expr_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    ExprReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.exprTransport

theorem stmt_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    StmtReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.stmtTransport

theorem block_ready_transport_of_normal
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt} :
    BlockReadyTransportGoal Γ Δ σ σ' head :=
  readinessTransportNormalCore.blockTransport

theorem seq_ready_right_after_left_normal_of_core
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    ScopedTypedStateConcrete Δ σ' →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    StmtReadyConcrete Δ σ' t :=
  readinessTransportNormalCore.seqRightAfterLeftNormal

theorem cons_block_ready_tail_after_head_normal_of_core
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Δ →
    ScopedTypedStateConcrete Δ σ' →
    BlockReadyConcrete Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    BlockReadyConcrete Δ σ' ss :=
  readinessTransportNormalCore.consTailAfterHeadNormal

end Cpp
