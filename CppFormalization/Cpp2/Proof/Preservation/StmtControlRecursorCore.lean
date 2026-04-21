import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ConditionalNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernelSupport

namespace Cpp

/-!
# Proof.Preservation.StmtControlRecursorCore

Common structural recursion core for
`StmtControlCompatible` / `BlockControlCompatible`.

The shared skeleton is theorem-backed for primitive / seq / ite / block and for
the non-recursive `while` leaves. The only variation point is the four genuinely
recursive `while` branches.
-/

abbrev WhileNormalNormalHandler : Prop :=
  ∀ {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂},
    StmtControlCompatible hN hbody →
    StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC) htail →
    (ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ body →
      ScopedTypedStateConcrete Γ σ₁) →
    (ScopedTypedStateConcrete Γ σ₁ →
      StmtReadyConcrete Γ σ₁ (.whileStmt c body) →
      ScopedTypedStateConcrete Γ σ₂) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ₂

abbrev WhileContinueNormalHandler : Prop :=
  ∀ {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hbody : BigStepStmt σ body .continueResult σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂},
    StmtControlCompatible hC hbody →
    StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC) htail →
    (ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ body →
      ScopedTypedStateConcrete Γ σ₁) →
    (ScopedTypedStateConcrete Γ σ₁ →
      StmtReadyConcrete Γ σ₁ (.whileStmt c body) →
      ScopedTypedStateConcrete Γ σ₂) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ₂

abbrev WhileNormalReturnHandler : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {rv : Option Value}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hR : HasTypeStmtCI .returnK Γ body Δ}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂},
    StmtControlCompatible hN hbody →
    StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR) htail →
    (ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ body →
      ScopedTypedStateConcrete Γ σ₁) →
    (ScopedTypedStateConcrete Γ σ₁ →
      StmtReadyConcrete Γ σ₁ (.whileStmt c body) →
      ScopedTypedStateConcrete Δ σ₂) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Δ σ₂

abbrev WhileContinueReturnHandler : Prop :=
  ∀ {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {rv : Option Value}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hR : HasTypeStmtCI .returnK Γ body Δ}
    {hbody : BigStepStmt σ body .continueResult σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂},
    StmtControlCompatible hC hbody →
    StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR) htail →
    (ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ body →
      ScopedTypedStateConcrete Γ σ₁) →
    (ScopedTypedStateConcrete Γ σ₁ →
      StmtReadyConcrete Γ σ₁ (.whileStmt c body) →
      ScopedTypedStateConcrete Δ σ₂) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Δ σ₂

structure WhileCompatHandlers where
  normalNormal : WhileNormalNormalHandler
  continueNormal : WhileContinueNormalHandler
  normalReturn : WhileNormalReturnHandler
  continueReturn : WhileContinueReturnHandler

structure StmtBlockPreservationKernel where
  stmt :
    ∀ {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
      {σ : State} {ctrl : CtrlResult} {σ' : State}
      {hty : HasTypeStmtCI k Γ s Δ}
      {hstep : BigStepStmt σ s ctrl σ'},
      StmtControlCompatible hty hstep →
      ScopedTypedStateConcrete Γ σ →
      StmtReadyConcrete Γ σ s →
      ScopedTypedStateConcrete Δ σ'
  block :
    ∀ {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
      {σ : State} {ctrl : CtrlResult} {σ' : State}
      {hty : HasTypeBlockCI k Γ ss Δ}
      {hstep : BigStepBlock σ ss ctrl σ'},
      BlockControlCompatible hty hstep →
      ScopedTypedStateConcrete Γ σ →
      BlockReadyConcrete Γ σ ss →
      ScopedTypedStateConcrete Δ σ'

mutual

private theorem stmt_control_goal_of_handlers
    (H : WhileCompatHandlers)
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  match hcomp with
  | .skip =>
      intro hσ _
      simpa using hσ

  | .exprStmt =>
      intro hσ hready
      rename_i Γ σ e τ hv
      exact
        primitive_stmt_normal_preserves_scoped_typed_state_concrete
          (st := .exprStmt _)
          (by simp)
          (HasTypeStmtCI.exprStmt hv)
          hσ hready hstep

  | .assign =>
      intro hσ hready
      rename_i Γ σ σ' p e τ hp hv
      exact
        primitive_stmt_normal_preserves_scoped_typed_state_concrete
          (st := .assign _ _)
          (by simp)
          (HasTypeStmtCI.assign hp hv)
          hσ hready hstep

  | .declareObjNone =>
      intro hσ hready
      rename_i Γ σ σ' τ x hfresh hobj
      exact
        primitive_stmt_normal_preserves_scoped_typed_state_concrete
          (st := .declareObj _ _ none)
          (by simp)
          (HasTypeStmtCI.declareObjNone hfresh hobj)
          hσ hready hstep

  | .declareObjSome =>
      intro hσ hready
      rename_i Γ σ σ' τ x e hfresh hobj hv
      exact
        primitive_stmt_normal_preserves_scoped_typed_state_concrete
          (st := .declareObj _ _ (some _))
          (by simp)
          (HasTypeStmtCI.declareObjSome hfresh hobj hv)
          hσ hready hstep

  | .declareRef =>
      intro hσ hready
      rename_i Γ σ σ' τ x p hfresh hp
      exact
        primitive_stmt_normal_preserves_scoped_typed_state_concrete
          (st := .declareRef _ _ _)
          (by simp)
          (HasTypeStmtCI.declareRef hfresh hp)
          hσ hready hstep

  | .breakStmt =>
      intro hσ _
      simpa using hσ

  | .continueStmt =>
      intro hσ _
      simpa using hσ

  | .returnNone =>
      intro hσ _
      simpa using hσ

  | .returnSome =>
      intro hσ _
      simpa using hσ

  | .seq_normal hcompS hcompT =>
      intro hσ hready
      have hreadyS := seq_ready_left hready
      have hσ₁ := stmt_control_goal_of_handlers H hcompS hσ hreadyS
      have hreadyT :=
        seq_ready_right_after_left_normal ‹_› hσ₁ hready ‹_›
      exact stmt_control_goal_of_handlers H hcompT hσ₁ hreadyT

  | .seq_break hcompS =>
      intro hσ hready
      have hreadyS := seq_ready_left hready
      exact stmt_control_goal_of_handlers H hcompS hσ hreadyS

  | .seq_continue hcompS =>
      intro hσ hready
      have hreadyS := seq_ready_left hready
      exact stmt_control_goal_of_handlers H hcompS hσ hreadyS

  | .seq_return hcompS =>
      intro hσ hready
      have hreadyS := seq_ready_left hready
      exact stmt_control_goal_of_handlers H hcompS hσ hreadyS

  | .ite_true hcompS =>
      intro hσ hready
      rcases ite_ready_branch_data hready with ⟨hreadyS, _⟩
      exact stmt_control_goal_of_handlers H hcompS hσ hreadyS

  | .ite_false hcompT =>
      intro hσ hready
      rcases ite_ready_branch_data hready with ⟨_, hreadyT⟩
      exact stmt_control_goal_of_handlers H hcompT hσ hreadyT

  | .while_false_normal =>
      intro hσ _
      simpa using hσ

  | .while_true_normal_normal (Γ := Γ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC)
      (hcond := hcond) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      intro hσ hready
      exact
        H.normalNormal
          (hc := hc) (hN := hN) (hB := hB) (hC := hC)
          (hbody := hbody) (htail := htail)
          hcompBody hcompTail
          (stmt_control_goal_of_handlers H hcompBody)
          (stmt_control_goal_of_handlers H hcompTail)
          hσ hready

  | .while_true_break hcompBody =>
      intro hσ hready
      exact whileBreakCase (stmt_control_goal_of_handlers H hcompBody) hσ hready

  | .while_true_continue_normal (Γ := Γ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC)
      (hcond := hcond) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      intro hσ hready
      exact
        H.continueNormal
          (hc := hc) (hN := hN) (hB := hB) (hC := hC)
          (hbody := hbody) (htail := htail)
          hcompBody hcompTail
          (stmt_control_goal_of_handlers H hcompBody)
          (stmt_control_goal_of_handlers H hcompTail)
          hσ hready

  | .while_true_normal_return (Γ := Γ) (Δ := Δ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
      (hcond := hcond) (rv := rv) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      intro hσ hready
      exact
        H.normalReturn
          (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
          (rv := rv) (hbody := hbody) (htail := htail)
          hcompBody hcompTail
          (stmt_control_goal_of_handlers H hcompBody)
          (stmt_control_goal_of_handlers H hcompTail)
          hσ hready

  | .while_true_continue_return (Γ := Γ) (Δ := Δ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
      (hcond := hcond) (rv := rv) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      intro hσ hready
      exact
        H.continueReturn
          (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
          (rv := rv) (hbody := hbody) (htail := htail)
          hcompBody hcompTail
          (stmt_control_goal_of_handlers H hcompBody)
          (stmt_control_goal_of_handlers H hcompTail)
          hσ hready

  | .while_true_return hcompBody =>
      intro hσ hready
      exact whileReturnLeafCase (stmt_control_goal_of_handlers H hcompBody) hσ hready

  | .block (Γ := Γ) (Θ := Θ) (ss := ss)
      (σ := σ) (σ₀ := σ₀) (σ₁ := σ₁) (σ₂ := σ₂) (ctrl := ctrl)
      (htyB := htyB) (hopen := hopen) (hbody := hbody) (hclose := hclose)
      hcompBody =>
      intro hσ hready
      exact
        blockStmtCase
          (htyB := htyB) (hopen := hopen) (hclose := hclose)
          (block_control_goal_of_handlers H hcompBody)
          hσ hready

private theorem block_control_goal_of_handlers
    (H : WhileCompatHandlers)
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' := by
  match hcomp with
  | .nil =>
      intro hσ _
      simpa using hσ

  | .cons_normal hcompS hcompT =>
      intro hσ hready
      have hreadyS := cons_block_ready_head hready
      have hσ₁ := stmt_control_goal_of_handlers H hcompS hσ hreadyS
      have hreadyT :=
        cons_block_ready_tail_after_head_normal ‹_› hσ₁ hready ‹_›
      exact block_control_goal_of_handlers H hcompT hσ₁ hreadyT

  | .cons_break hcompS =>
      intro hσ hready
      have hreadyS := cons_block_ready_head hready
      exact stmt_control_goal_of_handlers H hcompS hσ hreadyS

  | .cons_continue hcompS =>
      intro hσ hready
      have hreadyS := cons_block_ready_head hready
      exact stmt_control_goal_of_handlers H hcompS hσ hreadyS

  | .cons_return hcompS =>
      intro hσ hready
      have hreadyS := cons_block_ready_head hready
      exact stmt_control_goal_of_handlers H hcompS hσ hreadyS

end

def stmtBlock_preservation_kernel_of_handlers
    (H : WhileCompatHandlers) : StmtBlockPreservationKernel where
  stmt := by
    intro k Γ Δ s σ ctrl σ' hty hstep hcomp
    exact stmt_control_goal_of_handlers H hcomp
  block := by
    intro k Γ Δ ss σ ctrl σ' hty hstep hcomp
    exact block_control_goal_of_handlers H hcomp

end Cpp
