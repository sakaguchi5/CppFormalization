import CppFormalization.Cpp2.Proof.Preservation.StmtControlRecursorCore
--import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernelSupport
namespace Cpp

/-!
# Proof.Preservation.StmtControlKernel

Theorem-backed preservation kernel over compatibility derivations.

The old shell axioms are gone. The price is explicit: the kernel now requires
`WhileCtxProvider`, because the recursive `while` branches genuinely need the
extra local data encoded there.
-/

def whileCompatHandlers_kernel
   (mkWhileReentry : WhileReentryReadyProvider):
    WhileCompatHandlers where
  normalNormal := by
    intro Γ σ0 σ1 σ2 c body hc hN hB hC hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileNormalNormalCase
        mkWhileReentry hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

  continueNormal := by
    intro Γ σ0 σ1 σ2 c body hc hN hB hC hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileContinueNormalCase
        mkWhileReentry hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

  normalReturn := by
    intro Γ Δ σ0 σ1 σ2 c body rv hc hN hB hC hR hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileNormalReturnCase
        mkWhileReentry hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

  continueReturn := by
    intro Γ Δ σ0 σ1 σ2 c body rv hc hN hB hC hR hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileContinueReturnCase
        mkWhileReentry hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

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
