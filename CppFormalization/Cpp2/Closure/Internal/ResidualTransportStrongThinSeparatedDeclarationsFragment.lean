import CppFormalization.Cpp2.Closure.Internal.ResidualTransportStrongThinSeparatedFragment
import CppFormalization.Cpp2.Closure.Internal.ResidualTransportableDeclarationsFragment

namespace Cpp

/-!
Assignment-headed residual transport fragment with declaration suffixes and the
strong thin-separated condition replay.

This is the declaration-aware companion to
`ResidualTransportStrongThinSeparatedFragment`.

The idea is the same:
- the head is fixed to `.assign q rhs`;
- suffix read-places still use the old replay-stable restriction;
- suffix value/condition replay is upgraded from `ReplayStableCondExpr` to the
  typed family `StrongThinSeparatedCondExpr Γ σ q rhs`;
- declaration cases are kept explicit, since they are not the real frontier.

So this is the honest "assign-headed + deref-aware + declarations" fragment.
-/


/- =========================================================
   1. Assignment-headed transportable suffix fragment with declarations
   ========================================================= -/

inductive AssignHeadTransportableStmtDecl
    (Γ : TypeEnv) (σ : State) (q : PlaceExpr) (rhs : ValExpr) :
    CppStmt → Prop where
  | skip :
      AssignHeadTransportableStmtDecl Γ σ q rhs .skip
  | exprStmt {e : ValExpr} {τ : CppType} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
      ReplayStableReadPlace p →
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.assign p e)
  | declareObjNone {τ : CppType} {x : Ident} :
      AssignHeadTransportableStmtDecl Γ σ q rhs (.declareObj τ x none)
  | declareObjSome {τobj : CppType} {x : Ident} {e : ValExpr} {τe : CppType} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τe →
      HasValueType Γ e τe →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.declareObj τobj x (some e))
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} :
      ReplayStableReadPlace p →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.declareRef τ x p)
  | seq {s t : CppStmt} :
      AssignHeadTransportableStmtDecl Γ σ q rhs s →
      AssignHeadTransportableStmtDecl Γ σ q rhs t →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.seq s t)
  | ite {c : ValExpr} {s t : CppStmt} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmtDecl Γ σ q rhs s →
      AssignHeadTransportableStmtDecl Γ σ q rhs t →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.ite c s t)
  | whileStmt {c : ValExpr} {body : CppStmt} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmtDecl Γ σ q rhs body →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.whileStmt c body)
  | breakStmt :
      AssignHeadTransportableStmtDecl Γ σ q rhs .breakStmt
  | continueStmt :
      AssignHeadTransportableStmtDecl Γ σ q rhs .continueStmt
  | returnNone :
      AssignHeadTransportableStmtDecl Γ σ q rhs (.returnStmt none)
  | returnSome {e : ValExpr} {τ : CppType} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.returnStmt (some e))

inductive AssignHeadTransportableBlockDecl
    (Γ : TypeEnv) (σ : State) (q : PlaceExpr) (rhs : ValExpr) :
    StmtBlock → Prop where
  | nil :
      AssignHeadTransportableBlockDecl Γ σ q rhs .nil
  | cons {s : CppStmt} {ss : StmtBlock} :
      AssignHeadTransportableStmtDecl Γ σ q rhs s →
      AssignHeadTransportableBlockDecl Γ σ q rhs ss →
      AssignHeadTransportableBlockDecl Γ σ q rhs (.cons s ss)

/- =========================================================
   1.5 Push-scope stability of the current declaration-aware fragment
   ========================================================= -/

/--
Typing of value expressions is stable under pushing an empty type scope.

This is the minimal weakening bridge needed to transport the current
assign-headed declaration-aware fragment through block-entry.
-/
axiom hasValueType_pushTypeScope
    {Γ : TypeEnv} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    HasValueType (pushTypeScope Γ) e τ

/--
The strong thin-separated replay witness is stable under pushing an empty
type/runtime scope.

Mathematically this is natural: the new top scope is empty, so it does not
introduce aliases or invalidate the old replay witness.
-/
axiom strongThinSeparatedCondExpr_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs e : ValExpr} {τ : CppType} :
    StrongThinSeparatedCondExpr Γ σ q rhs e τ →
    StrongThinSeparatedCondExpr (pushTypeScope Γ) (pushScope σ) q rhs e τ

mutual

theorem assign_head_transportable_decl_stmt_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} {st : CppStmt} :
    AssignHeadTransportableStmtDecl Γ σ q rhs st →
    AssignHeadTransportableStmtDecl (pushTypeScope Γ) (pushScope σ) q rhs st := by
  intro h
  induction h with
  | skip =>
      exact .skip
  | exprStmt hc hty =>
      exact .exprStmt
        (strongThinSeparatedCondExpr_pushScope hc)
        (hasValueType_pushTypeScope hty)
  | assign hp hc hty =>
      exact .assign
        hp
        (strongThinSeparatedCondExpr_pushScope hc)
        (hasValueType_pushTypeScope hty)
  | declareObjNone =>
      exact .declareObjNone
  | declareObjSome hc hty =>
      exact .declareObjSome
        (strongThinSeparatedCondExpr_pushScope hc)
        (hasValueType_pushTypeScope hty)
  | declareRef hp =>
      exact .declareRef hp
  | seq hs ht ihs iht =>
      exact .seq ihs iht
  | ite hc hs ht ihs iht =>
      exact .ite
        (strongThinSeparatedCondExpr_pushScope hc)
        ihs iht
  | whileStmt hc hbody ih =>
      exact .whileStmt
        (strongThinSeparatedCondExpr_pushScope hc)
        ih
  | breakStmt =>
      exact .breakStmt
  | continueStmt =>
      exact .continueStmt
  | returnNone =>
      exact .returnNone
  | returnSome hc hty =>
      exact .returnSome
        (strongThinSeparatedCondExpr_pushScope hc)
        (hasValueType_pushTypeScope hty)

theorem assign_head_transportable_decl_block_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlockDecl Γ σ q rhs ss →
    AssignHeadTransportableBlockDecl (pushTypeScope Γ) (pushScope σ) q rhs ss := by
  intro h
  induction h with
  | nil =>
      exact .nil
  | cons hs hss ih =>
      exact .cons
        (assign_head_transportable_decl_stmt_pushScope hs)
        ih

end

/- =========================================================
   2. Replay across the fixed head assignment
   ========================================================= -/

theorem assign_head_transportable_decl_stmt_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {target : CppStmt} :
    AssignHeadTransportableStmtDecl Γ σ q rhs target →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ target →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' target := by
  intro htarget hσ' hready hstep
  induction htarget generalizing σ' with
  | skip =>
      exact StmtReadyConcrete.skip
  | exprStmt hc hty_hc =>
      cases hready with
      | exprStmt hty_ready heready =>
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact StmtReadyConcrete.exprStmt hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)
  | assign hp hc hty_hc =>
      cases hready with
      | assign hpty hpready hvty_ready heready =>
          have heq := hasValueType_unique hvty_ready hty_hc
          subst heq
          exact StmtReadyConcrete.assign
            hpty
            (replay_stable_read_place_ready_after_assign hp hσ' hpready hstep)
            hvty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)
  | declareObjNone =>
      cases hready with
      | declareObjNone hfresh hobj =>
          exact StmtReadyConcrete.declareObjNone hfresh hobj
  | declareObjSome hc hty_hc =>
      cases hready with
      | declareObjSome hfresh hobj hty_ready heready =>
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact StmtReadyConcrete.declareObjSome
            hfresh hobj hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)
  | declareRef hp =>
      cases hready with
      | declareRef hfresh hpty hpready =>
          exact StmtReadyConcrete.declareRef
            hfresh hpty
            (replay_stable_read_place_ready_after_assign hp hσ' hpready hstep)
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
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact StmtReadyConcrete.returnSome
            hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign
              hc hσ' heready hstep)

theorem assign_head_transportable_decl_block_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlockDecl Γ σ q rhs ss →
    ScopedTypedStateConcrete Γ σ' →
    BlockReadyConcrete Γ σ ss →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BlockReadyConcrete Γ σ' ss := by
  intro hblock hσ' hready hstep
  induction hblock generalizing σ' with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hs hss ih =>
      cases hready with
      | cons hreadyS hreadySS =>
          exact BlockReadyConcrete.cons
            (assign_head_transportable_decl_stmt_ready_after_assign_head
              hs hσ' hreadyS hstep)
            (ih hσ' hreadySS hstep)


/- =========================================================
   3. Residual boundary recovery for head = assign
   ========================================================= -/

theorem assign_head_transportable_decl_right_seq_normal_preserves_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {t : CppStmt} :
    AssignHeadTransportableStmtDecl Γ σ q rhs t →
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
    assign_head_transportable_decl_stmt_ready_after_assign_head
      hright hσ'Γ (seq_ready_right_declfrag hreadySeq) hstepHead
  exact ⟨Θ, htyRight, hσ'Γ, hreadyRight'⟩

theorem assign_head_transportable_decl_tail_cons_head_normal_preserves_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlockDecl Γ σ q rhs ss →
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
    assign_head_transportable_decl_block_ready_after_assign_head
      htail hσ'Γ (cons_block_ready_tail_declfrag hready) hstep
  exact ⟨Ξ, htyTail, hσ'Γ, hreadyTail'⟩

end Cpp
