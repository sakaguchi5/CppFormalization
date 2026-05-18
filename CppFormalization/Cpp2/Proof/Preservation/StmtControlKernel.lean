import CppFormalization.Cpp2.Proof.Preservation.StmtControlRecursorCore
import CppFormalization.Cpp2.Continuation.Boundary.LegacyTransport

namespace Cpp

/-!
# Proof.Preservation.StmtControlKernel

Theorem-backed preservation kernel over compatibility derivations.

The old shell axioms are gone. The price is explicit: the kernel now requires
`WhileCtxProvider`, because the recursive `while` branches genuinely need the
extra local data encoded there.

The `seq normal` and block `cons normal` handlers no longer use the legacy
exact-tail projections directly.  They project the pre-world tail readiness and
then construct statement/block continuation dynamic boundaries.
The temporary constructors still use the legacy `ReadinessTransportNormalCore`
obligation internally.  This shifts the remaining ordinary-readiness debt from the
specialized exact-tail axiom to the general readiness-transport family.
-/

def whileCompatHandlers_kernel
   (mkWhileReentry : WhileReentryReadyProvider):
    WhileCompatHandlers where
  seqNormal := by
    intro Γ Θ Δ σ σ₁ s t k htyHead hstepHead htyTail _hcompatHead ihHead hσ hreadySeq
    have hreadyHead : StmtReadyConcrete Γ σ s :=
      stmtControlRecursor_seq_ready_left hreadySeq
    have hσ₁ : ScopedTypedStateConcrete Θ σ₁ :=
      ihHead hσ hreadyHead
    have hreadyTailPre : StmtReadyConcrete Γ σ t :=
      seq_ready_right hreadySeq
    have hctx : NormalTransportCtx Γ Θ σ σ₁ s :=
      ⟨htyHead, hstepHead, hσ₁⟩
    have htailCont : StmtContinuationDynamicBoundary Θ σ₁ t :=
      stmt_continuation_dynamic_of_legacy_transport hctx htyTail hreadyTailPre
    have hreadyTail : StmtReadyConcrete Θ σ₁ t :=
      htailCont.safe
    exact ⟨htailCont.state, hreadyTail⟩

  consNormal := by
    intro Γ Θ Δ σ σ₁ s ss k htyHead hstepHead htyTail _hcompatHead ihHead hσ hreadyCons
    have hreadyHead : StmtReadyConcrete Γ σ s :=
      stmtControlRecursor_cons_block_ready_head hreadyCons
    have hσ₁ : ScopedTypedStateConcrete Θ σ₁ :=
      ihHead hσ hreadyHead
    have hreadyTailPre : BlockReadyConcrete Γ σ ss :=
      cons_block_ready_tail hreadyCons
    have hctx : NormalTransportCtx Γ Θ σ σ₁ s :=
      ⟨htyHead, hstepHead, hσ₁⟩
    have htailCont : BlockContinuationDynamicBoundary Θ σ₁ ss :=
      block_continuation_dynamic_of_legacy_transport hctx htyTail hreadyTailPre
    have hreadyTail : BlockReadyConcrete Θ σ₁ ss :=
      htailCont.safe
    exact ⟨htailCont.state, hreadyTail⟩

  normalNormal := by
    intro Γ σ0 σBody σTail c body hc hN hB hC hstepBody hstepLoopTail
      _hcompatBody _hcompatLoopTail ihBodyPres ihLoopPres hscIn hreadyWhile
    exact
      whileNormalNormalCase
        mkWhileReentry hc hN hB hC hstepBody ihBodyPres ihLoopPres
        hscIn hreadyWhile

  continueNormal := by
    intro Γ σ0 σBody σTail c body hc hN hB hC hstepBody hstepLoopTail
      _hcompatBody _hcompatLoopTail ihBodyPres ihLoopPres hscIn hreadyWhile
    exact
      whileContinueNormalCase
        mkWhileReentry hc hN hB hC hstepBody ihBodyPres ihLoopPres
        hscIn hreadyWhile

  normalReturn := by
    intro Γ Δ σ0 σBody σTail c body rv hc hN hB hC hR hstepBody hstepLoopTail
      _hcompatBody _hcompatLoopTail ihBodyPres ihLoopPres hscIn hreadyWhile
    exact
      whileNormalReturnCase
        mkWhileReentry hc hN hB hC hstepBody ihBodyPres ihLoopPres
        hscIn hreadyWhile

  continueReturn := by
    intro Γ Δ σ0 σBody σTail c body rv hc hN hB hC hR hstepBody hstepLoopTail
      _hcompatBody _hcompatLoopTail ihBodyPres ihLoopPres hscIn hreadyWhile
    exact
      whileContinueReturnCase
        mkWhileReentry hc hN hB hC hstepBody ihBodyPres ihLoopPres
        hscIn hreadyWhile

def stmtBlock_preservation_kernel
    (mkWhileReentry : WhileReentryReadyProvider):
    StmtBlockPreservationKernel :=
  stmtBlock_preservation_kernel_of_handlers (whileCompatHandlers_kernel mkWhileReentry)

theorem stmt_control_preserves_scoped_typed_state_of_compatible
    (mkWhileReentry : WhileReentryReadyProvider)
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' :=
  (stmtBlock_preservation_kernel mkWhileReentry).stmt hcomp

theorem block_control_preserves_scoped_typed_state_of_compatible
    (mkWhileReentry : WhileReentryReadyProvider)
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' :=
  (stmtBlock_preservation_kernel mkWhileReentry).block hcomp

end Cpp
