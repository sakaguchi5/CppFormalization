import CppFormalization.Cpp2.Closure.Internal.ReadinessTransportNormalCore

namespace Cpp

/-!
# Closure.Internal.ReadinessTransportNormalExactTail

Legacy exact tail-ready kernels split out of `ReadinessTransportNormalCore`.

These kernels are still consumed by the ordinary-readiness route in
`SequentialNormalPreservation` and `BlockBodyNormalPreservation`:

* after the left side of a sequence finishes normally, rebuild readiness for the
  right statement at the concrete post-state;
* after the head of a block finishes normally, rebuild readiness for the block
  tail at the concrete post-state.

They are intentionally separated from the general place/expr/stmt/block
transport family.  The demand route does not prove these exact readiness
transport statements; it replaces their use by carrying path-sensitive tail
demand at the actual post-state.
-/

structure ReadinessTransportNormalExactTail : Type where
  /--
  Legacy exact seq-tail kernel.

  Long-term target:
  callers should migrate to demand-side residual boundaries where possible.
  Ordinary readiness users may keep this as a separate debt item.
  -/
  seqRightAfterLeftNormal :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt},
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Δ σ' →
      StmtReadyConcrete Γ σ (.seq s t) →
      BigStepStmt σ s .normal σ' →
      StmtReadyConcrete Δ σ' t

  /--
  Legacy exact block-tail kernel.

  Long-term target:
  callers should migrate to demand-side residual boundaries where possible.
  Ordinary readiness users may keep this as a separate debt item.
  -/
  consTailAfterHeadNormal :
    ∀ {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock},
      HasTypeStmtCI .normalK Γ s Δ →
      ScopedTypedStateConcrete Δ σ' →
      BlockReadyConcrete Γ σ (.cons s ss) →
      BigStepStmt σ s .normal σ' →
      BlockReadyConcrete Δ σ' ss

/--
Single choke point for the remaining exact tail-ready debt.

This axiom was previously bundled inside `ReadinessTransportNormalCore`; it is
now isolated so that the core transport family can shrink independently.
-/
axiom readinessTransportNormalExactTail : ReadinessTransportNormalExactTail

/- =========================================================
   Preferred projection names
   ========================================================= -/

theorem seq_ready_right_after_left_normal_of_exact_tail
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    ScopedTypedStateConcrete Δ σ' →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    StmtReadyConcrete Δ σ' t :=
  readinessTransportNormalExactTail.seqRightAfterLeftNormal

theorem cons_block_ready_tail_after_head_normal_of_exact_tail
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Δ →
    ScopedTypedStateConcrete Δ σ' →
    BlockReadyConcrete Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    BlockReadyConcrete Δ σ' ss :=
  readinessTransportNormalExactTail.consTailAfterHeadNormal

/- =========================================================
   Compatibility projection names retained for current callers
   ========================================================= -/

theorem seq_ready_right_after_left_normal_of_core
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ s Δ →
    ScopedTypedStateConcrete Δ σ' →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    StmtReadyConcrete Δ σ' t :=
  seq_ready_right_after_left_normal_of_exact_tail

theorem cons_block_ready_tail_after_head_normal_of_core
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    HasTypeStmtCI .normalK Γ s Δ →
    ScopedTypedStateConcrete Δ σ' →
    BlockReadyConcrete Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    BlockReadyConcrete Δ σ' ss :=
  cons_block_ready_tail_after_head_normal_of_exact_tail

end Cpp
