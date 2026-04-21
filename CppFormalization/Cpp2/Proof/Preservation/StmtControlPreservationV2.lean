import CppFormalization.Cpp2.Proof.Preservation.StmtControlRecursorCore

namespace Cpp

/-!
# Proof.Preservation.StmtControlPreservationV2

Strong theorem-backed compatibility preservation.

This instantiates the common structural recursor with theorem-backed handlers
for the four recursive `while` branches via `WhileCtxProvider`.
-/

def whileCompatHandlers_v2
    (mkWhileCtx : WhileCtxProvider) :
    WhileCompatHandlers where
  normalNormal := by
    intro Γ σ0 σ1 σ2 c body hc hN hB hC hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileNormalNormalCase
        mkWhileCtx hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

  continueNormal := by
    intro Γ σ0 σ1 σ2 c body hc hN hB hC hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileContinueNormalCase
        mkWhileCtx hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

  normalReturn := by
    intro Γ Δ σ0 σ1 σ2 c body rv hc hN hB hC hR hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileNormalReturnCase
        mkWhileCtx hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

  continueReturn := by
    intro Γ Δ σ0 σ1 σ2 c body rv hc hN hB hC hR hbody htail
      _hcompBody _hcompTail ihBody ihTail hsc_in hreadyWhile
    exact
      whileContinueReturnCase
        mkWhileCtx hc hN hB hC hbody ihBody ihTail
        hsc_in hreadyWhile

theorem stmt_control_preserves_scoped_typed_state_of_compatible_core
    (mkWhileCtx : WhileCtxProvider)
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' :=
  (stmtBlock_preservation_kernel_of_handlers
    (whileCompatHandlers_v2 mkWhileCtx)).stmt hcomp

end Cpp
