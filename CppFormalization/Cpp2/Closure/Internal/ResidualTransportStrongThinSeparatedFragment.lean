import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StrongThinSeparatedCondReplay
import CppFormalization.Cpp2.Closure.Internal.ResidualTransportStableFragment
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
Residual transport fragment strengthened by the theoremized strong thin-separated
condition replay across a specific head assignment `q := rhs`.

This file does not try to solve every residual case. It isolates the next honest
gain after `StrongThinSeparatedCondReplay`:

- keep the old replay-stable read-place restriction on suffix *places*;
- replace condition/value-expression replay by the stronger assignment-centered
  deref-aware fragment;
- recover seq/block residual boundaries for the concrete head
  `.assign q rhs`.

So this is the direct bridge from the local separation story back into the
residual transport story.
-/


/- =========================================================
   1. Assignment-headed transportable suffix fragment
   ========================================================= -/

inductive AssignHeadTransportableStmt
    (Γ : TypeEnv) (σ : State) (q : PlaceExpr) (rhs : ValExpr) :
    CppStmt → Prop where
  | skip :
      AssignHeadTransportableStmt Γ σ q rhs .skip
  | exprStmt {e : ValExpr} {τ : CppType} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmt Γ σ q rhs (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      ReplayStableReadPlace p →
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmt Γ σ q rhs (.assign p e)
  | seq {s t : CppStmt} :
      AssignHeadTransportableStmt Γ σ q rhs s →
      AssignHeadTransportableStmt Γ σ q rhs t →
      AssignHeadTransportableStmt Γ σ q rhs (.seq s t)
  | ite {c : ValExpr} {s t : CppStmt} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmt Γ σ q rhs s →
      AssignHeadTransportableStmt Γ σ q rhs t →
      AssignHeadTransportableStmt Γ σ q rhs (.ite c s t)
  | whileStmt {c : ValExpr} {body : CppStmt} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmt Γ σ q rhs body →
      AssignHeadTransportableStmt Γ σ q rhs (.whileStmt c body)
  | breakStmt :
      AssignHeadTransportableStmt Γ σ q rhs .breakStmt
  | continueStmt :
      AssignHeadTransportableStmt Γ σ q rhs .continueStmt
  | returnNone :
      AssignHeadTransportableStmt Γ σ q rhs (.returnStmt none)
  | returnSome {e : ValExpr} {τ : CppType} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmt Γ σ q rhs (.returnStmt (some e))

inductive AssignHeadTransportableBlock
    (Γ : TypeEnv) (σ : State) (q : PlaceExpr) (rhs : ValExpr) :
    StmtBlock → Prop where
  | nil :
      AssignHeadTransportableBlock Γ σ q rhs .nil
  | cons {s : CppStmt} {ss : StmtBlock} :
      AssignHeadTransportableStmt Γ σ q rhs s →
      AssignHeadTransportableBlock Γ σ q rhs ss →
      AssignHeadTransportableBlock Γ σ q rhs (.cons s ss)


/- =========================================================
   2. Replay across the fixed head assignment
   ========================================================= -/

theorem assign_head_transportable_stmt_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {target : CppStmt} :
    AssignHeadTransportableStmt Γ σ q rhs target →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ target →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' target := by
  intro htarget hσ' hready hstep
  induction htarget generalizing  σ' with
  | skip =>
      exact StmtReadyConcrete.skip
  | exprStmt hc hty_hc =>
      cases hready with
      | exprStmt hty_ready heready =>
          -- 1. hc の型 (τ✝¹) と hready の型 (τ✝) が同じであることを導く
          have heq := hasValueType_unique hty_ready hty_hc
          -- 2. 型変数を統一する
          subst heq
          -- 3. 型が一致したので、関数を適用できる
          exact StmtReadyConcrete.exprStmt hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)
  | assign hp hc hty_hc =>
      cases hready with
      | assign hpty hpready hvty_ready heready =>
          -- 型の不一致を解消
          have heq := hasValueType_unique hvty_ready hty_hc
          subst heq
          exact StmtReadyConcrete.assign
            hpty
            (replay_stable_read_place_ready_after_assign hp hσ' hpready hstep)
            hvty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)
  | seq hs ht ihS ihT =>
      cases hready with
      | seq hreadyS hreadyT =>
          exact StmtReadyConcrete.seq
            (ihS hσ' hreadyS hstep)
            (ihT hσ' hreadyT hstep)
  | ite hc hs ht ihS ihT =>
      cases hready with
      | ite hcty hcready hreadyS hreadyT =>
          exact StmtReadyConcrete.ite
            hcty
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' hcready hstep)
            (ihS hσ' hreadyS hstep)
            (ihT hσ' hreadyT hstep)
  | whileStmt hc hbody ihBody =>
      cases hready with
      | whileStmt hcty hcready hreadyBody =>
          exact StmtReadyConcrete.whileStmt
            hcty
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' hcready hstep)
            (ihBody hσ' hreadyBody hstep)
  | breakStmt =>
      exact StmtReadyConcrete.breakStmt
  | continueStmt =>
      exact StmtReadyConcrete.continueStmt
  | returnNone =>
      exact StmtReadyConcrete.returnNone
  | returnSome hc hty_hc =>
      cases hready with
      | returnSome hty_ready heready =>
          -- 型の不一致を解消
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact StmtReadyConcrete.returnSome
            hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)

theorem assign_head_transportable_block_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlock Γ σ q rhs ss →
    ScopedTypedStateConcrete Γ σ' →
    BlockReadyConcrete Γ σ ss →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BlockReadyConcrete Γ σ' ss := by
  intro hblock hσ' hready hstep
  induction hblock generalizing  σ' with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hs hss ih =>
      cases hready with
      | cons hreadyS hreadySS =>
          exact BlockReadyConcrete.cons
            (assign_head_transportable_stmt_ready_after_assign_head
              hs hσ' hreadyS hstep)
            (ih hσ' hreadySS hstep)


/- =========================================================
   3. Residual boundary recovery for head = assign
   ========================================================= -/

theorem assign_stmt_env_preserving
    {Γ Δ : TypeEnv} {q : PlaceExpr} {rhs : ValExpr} :
    HasTypeStmtCI .normalK Γ (.assign q rhs) Δ →
    Δ = Γ := by
  intro hty
  cases hty
  rfl

theorem assign_head_transportable_right_seq_normal_preserves_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {t : CppStmt} :
    AssignHeadTransportableStmt Γ σ q rhs t →
    HasTypeStmtCI .normalK Γ (.seq (.assign q rhs) t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq (.assign q rhs) t) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro hright htySeq hσ hreadySeq hstepHead
  rcases seq_typing_data htySeq with ⟨Θ, htyHead, htyRight⟩
  have hΘ : Θ = Γ := by
    exact assign_stmt_env_preserving htyHead
  subst hΘ
  have hσ'Γ : ScopedTypedStateConcrete Θ σ' :=
    assign_stmt_normal_preserves_scoped_typed_state_concrete
      htyHead hσ (seq_ready_left hreadySeq) hstepHead
  have hreadyRight' : StmtReadyConcrete Θ σ' t :=
    assign_head_transportable_stmt_ready_after_assign_head
      hright hσ'Γ (seq_ready_right hreadySeq) hstepHead
  exact ⟨Θ, htyRight, hσ'Γ, hreadyRight'⟩

theorem assign_head_transportable_tail_cons_head_normal_preserves_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlock Γ σ q rhs ss →
    HasTypeBlockCI .normalK Γ (.cons (.assign q rhs) ss) Θ →
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ (.cons (.assign q rhs) ss) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ConsResidualBoundary Θ σ' ss := by
  intro htail hty hσ hready hstep
  rcases cons_block_typing_data hty with ⟨Ξ, htyHead, htyTail⟩
  have hΞ : Ξ = Γ := by
    exact assign_stmt_env_preserving htyHead
  subst hΞ
  have hσ'Γ : ScopedTypedStateConcrete Ξ σ' :=
    assign_stmt_normal_preserves_scoped_typed_state_concrete
      htyHead hσ (cons_block_ready_head hready) hstep
  have hreadyTail' : BlockReadyConcrete Ξ σ' ss :=
    assign_head_transportable_block_ready_after_assign_head
      htail hσ'Γ (cons_block_ready_tail hready) hstep
  exact ⟨Ξ, htyTail, hσ'Γ, hreadyTail'⟩

end Cpp
