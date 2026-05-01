
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

Naming convention inside this file:
- `handlers` is the externally supplied while-branch handler package.
- `hcompatHead` / `hcompatTail` are sequential or block-cons compatibility proofs.
- `hcompatBody` / `hcompatLoopTail` are while body and recursive loop-tail compatibility proofs.
- `ihBodyPres` / `ihLoopPres` are preservation IHs derived from those compatibility proofs.
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
    (handlers : WhileCompatHandlers)
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcompat : StmtControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ s →
    ScopedTypedStateConcrete Δ σ' := by
  match hcompat with
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

  | .seq_normal
      (Γ := Γ) (Θ := Θ) (Δ := Δ) (s := s) (t := t)
      (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (ctrl := ctrl)
      (htyS := htyHead) (htyT := htyTail)
      (hstepS := hstepHead) (hstepT := hstepTail)
      hcompatHead hcompatTail =>
      intro hσ hready
      have hpost :
          ScopedTypedStateConcrete Θ σ₁ ∧ StmtReadyConcrete Θ σ₁ t := by
        exact
          seq_left_normal_preserves_ready_of_left_preservation
            (Γ := Γ) (Δ := Θ) (σ := σ) (σ' := σ₁) (s := s) (t := t)
            (hpres := by
              intro _htyHead hσ0 hreadyHead0 _hstepHead
              exact stmt_control_goal_of_handlers handlers hcompatHead hσ0 hreadyHead0)
            htyHead hready hstepHead hσ
      rcases hpost with ⟨hσ₁, hreadyTail⟩
      exact stmt_control_goal_of_handlers handlers hcompatTail hσ₁ hreadyTail

  | .seq_break hcompatHead =>
      intro hσ hready
      have hreadyHead := seq_ready_left hready
      exact stmt_control_goal_of_handlers handlers hcompatHead hσ hreadyHead

  | .seq_continue hcompatHead =>
      intro hσ hready
      have hreadyHead := seq_ready_left hready
      exact stmt_control_goal_of_handlers handlers hcompatHead hσ hreadyHead

  | .seq_return hcompatHead =>
      intro hσ hready
      have hreadyHead := seq_ready_left hready
      exact stmt_control_goal_of_handlers handlers hcompatHead hσ hreadyHead

  | .ite_true hcompatThen =>
      intro hσ hready
      rcases ite_ready_branch_data hready with ⟨hreadyThen, _⟩
      exact stmt_control_goal_of_handlers handlers hcompatThen hσ hreadyThen

  | .ite_false hcompatElse =>
      intro hσ hready
      rcases ite_ready_branch_data hready with ⟨_, hreadyElse⟩
      exact stmt_control_goal_of_handlers handlers hcompatElse hσ hreadyElse

  | .while_false_normal =>
      intro hσ _
      simpa using hσ

  | .while_true_normal_normal (Γ := Γ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC)
      (hcond := hcond) (hbody := hstepBody) (htail := hstepLoopTail)
      hcompatBody hcompatLoopTail =>
      intro hσ hready
      exact
        handlers.normalNormal
          (hc := hc) (hN := hN) (hB := hB) (hC := hC)
          (hbody := hstepBody) (htail := hstepLoopTail)
          hcompatBody hcompatLoopTail
          (stmt_control_goal_of_handlers handlers hcompatBody)
          (stmt_control_goal_of_handlers handlers hcompatLoopTail)
          hσ hready

  | .while_true_break hcompatBody =>
      intro hσ hready
      exact whileBreakCase (stmt_control_goal_of_handlers handlers hcompatBody) hσ hready

  | .while_true_continue_normal (Γ := Γ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC)
      (hcond := hcond) (hbody := hstepBody) (htail := hstepLoopTail)
      hcompatBody hcompatLoopTail =>
      intro hσ hready
      exact
        handlers.continueNormal
          (hc := hc) (hN := hN) (hB := hB) (hC := hC)
          (hbody := hstepBody) (htail := hstepLoopTail)
          hcompatBody hcompatLoopTail
          (stmt_control_goal_of_handlers handlers hcompatBody)
          (stmt_control_goal_of_handlers handlers hcompatLoopTail)
          hσ hready

  | .while_true_normal_return (Γ := Γ) (Δ := Δ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
      (hcond := hcond) (rv := rv) (hbody := hstepBody) (htail := hstepLoopTail)
      hcompatBody hcompatLoopTail =>
      intro hσ hready
      exact
        handlers.normalReturn
          (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
          (rv := rv) (hbody := hstepBody) (htail := hstepLoopTail)
          hcompatBody hcompatLoopTail
          (stmt_control_goal_of_handlers handlers hcompatBody)
          (stmt_control_goal_of_handlers handlers hcompatLoopTail)
          hσ hready

  | .while_true_continue_return (Γ := Γ) (Δ := Δ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
      (hcond := hcond) (rv := rv) (hbody := hstepBody) (htail := hstepLoopTail)
      hcompatBody hcompatLoopTail =>
      intro hσ hready
      exact
        handlers.continueReturn
          (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
          (rv := rv) (hbody := hstepBody) (htail := hstepLoopTail)
          hcompatBody hcompatLoopTail
          (stmt_control_goal_of_handlers handlers hcompatBody)
          (stmt_control_goal_of_handlers handlers hcompatLoopTail)
          hσ hready

  | .while_true_return hcompatBody =>
      intro hσ hready
      exact whileReturnLeafCase (stmt_control_goal_of_handlers handlers hcompatBody) hσ hready

  | .block (Γ := Γ) (Θ := Θ) (ss := ss)
      (σ := σ) (σ₀ := σ₀) (σ₁ := σ₁) (σ₂ := σ₂) (ctrl := ctrl)
      (htyB := htyBlockBody) (hopen := hopen) (hbody := hstepBlockBody) (hclose := hclose)
      hcompatBlockBody =>
      intro hσ hready
      exact
        blockStmtCase
          (htyB := htyBlockBody) (hopen := hopen) (hclose := hclose)
          (block_control_goal_of_handlers handlers hcompatBlockBody)
          hσ hready

private theorem block_control_goal_of_handlers
    (handlers : WhileCompatHandlers)
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcompat : BlockControlCompatible hty hstep) :
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ ss →
    ScopedTypedStateConcrete Δ σ' := by
  match hcompat with
  | .nil =>
      intro hσ _
      simpa using hσ

  | .cons_normal
      (k := k) (Γ := Γ) (Θ := Θ) (Δ := Δ) (s := s) (ss := ss)
      (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (ctrl := ctrl)
      (htyS := htyHead) (htyT := htyTail)
      (hstepS := hstepHead) (hstepT := hstepTail)
      hcompatHead hcompatTail =>
      intro hσ hready
      have hpost :
          ScopedTypedStateConcrete Θ σ₁ ∧ BlockReadyConcrete Θ σ₁ ss := by
        exact
          cons_head_normal_preserves_ready_of_head_preservation
            (Γ := Γ) (Ξ := Θ) (σ := σ) (σ' := σ₁) (s := s) (ss := ss)
            (hpres := by
              intro _htyHead hσ0 hreadyHead0 _hstepHead
              exact stmt_control_goal_of_handlers handlers hcompatHead hσ0 hreadyHead0)
            htyHead hready hstepHead hσ
      rcases hpost with ⟨hσ₁, hreadyTail⟩
      exact block_control_goal_of_handlers handlers hcompatTail hσ₁ hreadyTail

  | .cons_break hcompatHead =>
      intro hσ hready
      have hreadyHead := cons_block_ready_head hready
      exact stmt_control_goal_of_handlers handlers hcompatHead hσ hreadyHead

  | .cons_continue hcompatHead =>
      intro hσ hready
      have hreadyHead := cons_block_ready_head hready
      exact stmt_control_goal_of_handlers handlers hcompatHead hσ hreadyHead

  | .cons_return hcompatHead =>
      intro hσ hready
      have hreadyHead := cons_block_ready_head hready
      exact stmt_control_goal_of_handlers handlers hcompatHead hσ hreadyHead

end

def stmtBlock_preservation_kernel_of_handlers
    (handlers : WhileCompatHandlers) : StmtBlockPreservationKernel where
  stmt := by
    intro k Γ Δ s σ ctrl σ' hty hstep hcompat
    exact stmt_control_goal_of_handlers handlers hcompat
  block := by
    intro k Γ Δ ss σ ctrl σ' hty hstep hcompat
    exact block_control_goal_of_handlers handlers hcompat

end Cpp
