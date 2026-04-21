import CppFormalization.Cpp2.Proof.Preservation.StmtControlWhileCompatShell
import CppFormalization.Cpp2.Proof.Preservation.StmtControlRecursorCore

namespace Cpp

/-!
# Proof.Preservation.StmtControlKernel

Lightweight preservation kernel over compatibility derivations.

All theorem-backed structural cases are shared through
`StmtControlRecursorCore`. The only remaining honest debt is the four open
recursive `while` branches, supplied here from
`StmtControlWhileCompatShell`.
-/

def whileCompatHandlers_shell : WhileCompatHandlers where
  normalNormal := by
    intro Γ σ σ₁ σ₂ c body hc hN hB hC hbody htail
      hcompBody hcompTail _ihBody _ihTail hσ hready
    exact
      while_true_normal_normal_goal
        (hc := hc) (hN := hN) (hB := hB) (hC := hC)
        (hbody := hbody) (htail := htail)
        hcompBody hcompTail hσ hready

  continueNormal := by
    intro Γ σ σ₁ σ₂ c body hc hN hB hC hbody htail
      hcompBody hcompTail _ihBody _ihTail hσ hready
    exact
      while_true_continue_normal_goal
        (hc := hc) (hN := hN) (hB := hB) (hC := hC)
        (hbody := hbody) (htail := htail)
        hcompBody hcompTail hσ hready

  normalReturn := by
    intro Γ Δ σ σ₁ σ₂ c body rv hc hN hB hC hR hbody htail
      hcompBody hcompTail _ihBody _ihTail hσ hready
    exact
      while_true_normal_return_goal
        (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
        (hbody := hbody) (htail := htail)
        hcompBody hcompTail hσ hready

  continueReturn := by
    intro Γ Δ σ σ₁ σ₂ c body rv hc hN hB hC hR hbody htail
      hcompBody hcompTail _ihBody _ihTail hσ hready
    exact
      while_true_continue_return_goal
        (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
        (hbody := hbody) (htail := htail)
        hcompBody hcompTail hσ hready

def stmtBlock_preservation_kernel : StmtBlockPreservationKernel :=
  stmtBlock_preservation_kernel_of_handlers whileCompatHandlers_shell

theorem stmt_control_preserves_scoped_typed_state_of_compatible
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' :=
  (stmtBlock_preservation_kernel).stmt hcomp

theorem block_control_preserves_scoped_typed_state_of_compatible
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' :=
  (stmtBlock_preservation_kernel).block hcomp

end Cpp
