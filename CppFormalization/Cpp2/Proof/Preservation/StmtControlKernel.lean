import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ConditionalNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.BlockNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility
import CppFormalization.Cpp2.Proof.Preservation.StmtControlWhileCompatShell
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernelSupport

namespace Cpp

/-!
# Proof.Preservation.StmtControlKernel

preservation kernel は statement / block の syntax recursion ではなく、
`StmtControlCompatible` / `BlockControlCompatible` の導出木に対する
structural induction で閉じる。

これにより mutual recursive theorem に対する termination 問題を避けつつ、
abrupt control での path-sensitive post-environment を正面から扱う。

重要:
- primitive / seq / ite / block はこのファイルで theorem-backed に閉じる。
- while については、旧 generic residual-readiness axiom を削除した結果、
  generic kernel としては前提が弱すぎる。
- 新設計では `LoopBodyBoundaryCI` と `LoopReentryKernelCI` が必要になるので、
  generic compatibility kernel 側では while 4分岐だけを honest obligation
  として外部 shell に切り出す。
-/

private def StmtCompatGoal
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (_hcomp : StmtControlCompatible hty hstep) : Prop :=
  ScopedTypedStateConcrete Γ σ →
  StmtReadyConcrete Γ σ s →
  ScopedTypedStateConcrete Δ σ'

private def BlockCompatGoal
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (_hcomp : BlockControlCompatible hty hstep) : Prop :=
  ScopedTypedStateConcrete Γ σ →
  BlockReadyConcrete Γ σ ss →
  ScopedTypedStateConcrete Δ σ'

mutual

private theorem stmt_control_goal
    {k : ControlKind} {Γ Δ : TypeEnv} {s : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ s Δ}
    {hstep : BigStepStmt σ s ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep) :
    StmtCompatGoal hcomp :=
  match hcomp with
  | .skip =>
      fun hσ _ => by simpa using hσ

  | .exprStmt =>
      fun hσ hready => by
        rename_i Γ σ e τ hv
        exact
          primitive_stmt_normal_preserves_scoped_typed_state_concrete
            (st := .exprStmt _)
            (by simp)
            (HasTypeStmtCI.exprStmt hv)
            hσ hready hstep

  | .assign =>
      fun hσ hready => by
        rename_i Γ σ σ' p e τ hp hv
        exact
          primitive_stmt_normal_preserves_scoped_typed_state_concrete
            (st := .assign _ _)
            (by simp)
            (HasTypeStmtCI.assign hp hv)
            hσ hready hstep

  | .declareObjNone =>
      fun hσ hready => by
        rename_i Γ σ σ' τ x hfresh hobj
        exact
          primitive_stmt_normal_preserves_scoped_typed_state_concrete
            (st := .declareObj _ _ none)
            (by simp)
            (HasTypeStmtCI.declareObjNone hfresh hobj)
            hσ hready hstep

  | .declareObjSome =>
      fun hσ hready => by
        rename_i Γ σ σ' τ x e hfresh hobj hv
        exact
          primitive_stmt_normal_preserves_scoped_typed_state_concrete
            (st := .declareObj _ _ (some _))
            (by simp)
            (HasTypeStmtCI.declareObjSome hfresh hobj hv)
            hσ hready hstep

  | .declareRef =>
      fun hσ hready => by
        rename_i Γ σ σ' τ x p hfresh hp
        exact
          primitive_stmt_normal_preserves_scoped_typed_state_concrete
            (st := .declareRef _ _ _)
            (by simp)
            (HasTypeStmtCI.declareRef hfresh hp)
            hσ hready hstep

  | .breakStmt =>
      fun hσ _ => by simpa using hσ

  | .continueStmt =>
      fun hσ _ => by simpa using hσ

  | .returnNone =>
      fun hσ _ => by simpa using hσ

  | .returnSome =>
      fun hσ _ => by simpa using hσ

  | .seq_normal hcompS hcompT =>
      fun hσ hready => by
        have hreadyS := seq_ready_left hready
        have hσ₁ := stmt_control_goal hcompS hσ hreadyS
        have hreadyT :=
          seq_ready_right_after_left_normal ‹_› hσ₁ hready ‹_›
        exact stmt_control_goal hcompT hσ₁ hreadyT

  | .seq_break hcompS =>
      fun hσ hready => by
        have hreadyS := seq_ready_left hready
        exact stmt_control_goal hcompS hσ hreadyS

  | .seq_continue hcompS =>
      fun hσ hready => by
        have hreadyS := seq_ready_left hready
        exact stmt_control_goal hcompS hσ hreadyS

  | .seq_return hcompS =>
      fun hσ hready => by
        have hreadyS := seq_ready_left hready
        exact stmt_control_goal hcompS hσ hreadyS

  | .ite_true hcompS =>
      fun hσ hready => by
        rcases ite_ready_branch_data hready with ⟨hreadyS, _⟩
        exact stmt_control_goal hcompS hσ hreadyS

  | .ite_false hcompT =>
      fun hσ hready => by
        rcases ite_ready_branch_data hready with ⟨_, hreadyT⟩
        exact stmt_control_goal hcompT hσ hreadyT

  | .while_false_normal =>
      fun hσ _ => by simpa using hσ

  | .while_true_normal_normal (Γ := Γ) (σ := σ) (σ₁ := σ₁) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC)
      (hcond := hcond) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      fun hσ hready => by
        exact
          while_true_normal_normal_goal
            (hc := hc) (hN := hN) (hB := hB) (hC := hC)
            (hcond := hcond) (hbody := hbody) (htail := htail)
            hcompBody hcompTail hσ hready

  | .while_true_break hcompBody =>
      fun hσ hready => by
        rename_i Γ σ σ₁ c body hc hN hB hC hcond hbody
        have hreadyBody : StmtReadyConcrete Γ σ body :=
          while_ready_body_data hready
        exact stmt_control_goal hcompBody hσ hreadyBody

  | .while_true_continue_normal (Γ := Γ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hcond := hcond) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      fun hσ hready => by
        exact
          while_true_continue_normal_goal
            (hc := hc) (hN := hN) (hB := hB) (hC := hC)
            (hcond := hcond) (hbody := hbody) (htail := htail)
            hcompBody hcompTail hσ hready

  | .while_true_normal_return (Γ := Γ) (Δ := Δ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR) (hcond := hcond) (rv := rv) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      fun hσ hready => by
        exact
          while_true_normal_return_goal
            (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
            (hcond := hcond) (hbody := hbody) (htail := htail)
            hcompBody hcompTail hσ hready

  | .while_true_continue_return (Γ := Γ) (Δ := Δ) (σ := σ) (σ₁ := σ₁) (σ₂ := σ₂) (c := c) (body := body)
      (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR) (hcond := hcond) (rv := rv) (hbody := hbody) (htail := htail)
      hcompBody hcompTail =>
      fun hσ hready => by
        exact
          while_true_continue_return_goal
            (hc := hc) (hN := hN) (hB := hB) (hC := hC) (hR := hR)
            (hcond := hcond) (hbody := hbody) (htail := htail)
            hcompBody hcompTail hσ hready

  | .while_true_return hcompBody =>
      fun hσ hready => by
        rename_i Γ Δ σ σ₁ c body rv hc hN hB hC hR hcond hbody
        have hreadyBody : StmtReadyConcrete Γ σ body :=
          while_ready_body_data hready
        exact stmt_control_goal hcompBody hσ hreadyBody

  | .block (Γ := Γ) (Θ := Θ) (ss := ss)
    (σ := σ) (σ₀ := σ₀) (σ₁ := σ₁) (σ₂ := σ₂) (ctrl := ctrl)
    (htyB := htyB) (hopen := hopen) (hbody := hbody) (hclose := hclose)
    hcompBody =>
    fun hσ hready => by
      exact
        blockStmtCase
          (htyB := htyB) (hopen := hopen) (hclose := hclose)
          (block_control_goal hcompBody)
          hσ hready

private theorem block_control_goal
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep) :
    BlockCompatGoal hcomp :=
  match hcomp with
  | .nil =>
      fun hσ _ => by simpa using hσ

  | .cons_normal hcompS hcompT =>
      fun hσ hready => by
        have hreadyS := cons_block_ready_head hready
        have hσ₁ := stmt_control_goal hcompS hσ hreadyS
        have hreadyT :=
          cons_block_ready_tail_after_head_normal ‹_› hσ₁ hready ‹_›
        exact block_control_goal hcompT hσ₁ hreadyT

  | .cons_break hcompS =>
      fun hσ hready => by
        have hreadyS := cons_block_ready_head hready
        exact stmt_control_goal hcompS hσ hreadyS

  | .cons_continue hcompS =>
      fun hσ hready => by
        have hreadyS := cons_block_ready_head hready
        exact stmt_control_goal hcompS hσ hreadyS

  | .cons_return hcompS =>
      fun hσ hready => by
        have hreadyS := cons_block_ready_head hready
        exact stmt_control_goal hcompS hσ hreadyS

end

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

def stmtBlock_preservation_kernel : StmtBlockPreservationKernel := by
  refine
    { stmt := ?_
      block := ?_ }
  · intro k Γ Δ s σ ctrl σ' hty hstep hcomp
    exact stmt_control_goal hcomp
  · intro k Γ Δ ss σ ctrl σ' hty hstep hcomp
    exact block_control_goal hcomp

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
