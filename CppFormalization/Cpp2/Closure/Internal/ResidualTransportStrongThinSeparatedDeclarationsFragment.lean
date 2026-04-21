import CppFormalization.Cpp2.Closure.Internal.AssignHeadPushScopeBridges
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

mutual

inductive AssignHeadTransportableStmtDecl :
    TypeEnv → State → PlaceExpr → ValExpr → CppStmt → Prop where
  | skip {Γ σ q rhs} :
      AssignHeadTransportableStmtDecl Γ σ q rhs .skip
  | exprStmt {Γ σ q rhs e τ} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.exprStmt e)
  | assign {Γ σ q rhs p e τ} :
      ReplayStableReadPlace p →
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.assign p e)
  | declareObjNone {Γ σ q rhs τ x} :
      AssignHeadTransportableStmtDecl Γ σ q rhs (.declareObj τ x none)
  | declareObjSome {Γ σ q rhs τobj x e τe} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τe →
      HasValueType Γ e τe →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.declareObj τobj x (some e))
  | declareRef {Γ σ q rhs τ x p} :
      ReplayStableReadPlace p →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.declareRef τ x p)
  | seq {Γ σ q rhs s t} :
      AssignHeadTransportableStmtDecl Γ σ q rhs s →
      AssignHeadTransportableStmtDecl Γ σ q rhs t →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.seq s t)
  | ite {Γ σ q rhs c s t} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmtDecl Γ σ q rhs s →
      AssignHeadTransportableStmtDecl Γ σ q rhs t →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.ite c s t)
  | whileStmt {Γ σ q rhs c body} :
      StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
      AssignHeadTransportableStmtDecl Γ σ q rhs body →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.whileStmt c body)
  | block {Γ σ q rhs ss} :
      AssignHeadTransportableBlockDecl (pushTypeScope Γ) (pushScope σ) q rhs ss →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.block ss)
  | breakStmt {Γ σ q rhs} :
      AssignHeadTransportableStmtDecl Γ σ q rhs .breakStmt
  | continueStmt {Γ σ q rhs} :
      AssignHeadTransportableStmtDecl Γ σ q rhs .continueStmt
  | returnNone {Γ σ q rhs} :
      AssignHeadTransportableStmtDecl Γ σ q rhs (.returnStmt none)
  | returnSome {Γ σ q rhs e τ} :
      StrongThinSeparatedCondExpr Γ σ q rhs e τ →
      HasValueType Γ e τ →
      AssignHeadTransportableStmtDecl Γ σ q rhs (.returnStmt (some e))

inductive AssignHeadTransportableBlockDecl :
    TypeEnv → State → PlaceExpr → ValExpr → StmtBlock → Prop where
  | nil {Γ σ q rhs} :
      AssignHeadTransportableBlockDecl Γ σ q rhs .nil
  | cons {Γ σ q rhs s ss} :
      AssignHeadTransportableStmtDecl Γ σ q rhs s →
      AssignHeadTransportableBlockDecl Γ σ q rhs ss →
      AssignHeadTransportableBlockDecl Γ σ q rhs (.cons s ss)

end


/- =========================================================
   1.5 Push-scope stability of the declaration-aware witness family
   ========================================================= -/

def ThinSeparatedWitness.pushScope
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    ThinSeparatedWitness Γ σ q rhs e τ →
    ThinSeparatedWitness (pushTypeScope Γ) (pushScope σ) q rhs e τ
  | w =>
      { ptrType := hasValueType_pushTypeScope w.ptrType
        srcStable := w.srcStable
        writeAddr := w.writeAddr
        writesQ := bigStepPlace_pushScope w.writesQ
        targetSeparated := by
          intro a hvalPush
          exact w.targetSeparated (bigStepValue_of_pushScope hvalPush) }

def LoadThinSeparatedWitness.pushScope
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {τ : CppType} :
    LoadThinSeparatedWitness Γ σ q rhs p τ →
    LoadThinSeparatedWitness (pushTypeScope Γ) (pushScope σ) q rhs p τ
  | w =>
      { base := w.base.pushScope
        sourceSeparated := by
          intro aSrc hplacePush
          exact w.sourceSeparated (bigStepPlace_of_pushScope hplacePush) }

def StrongThinSeparatedWitness.pushScope
    {Γ : TypeEnv} {σ : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    StrongThinSeparatedWitness Γ σ q rhs e τ →
    StrongThinSeparatedWitness (pushTypeScope Γ) (pushScope σ) q rhs e τ
  | .addrOf w => .addrOf w.pushScope
  | .load w => .load w.pushScope

theorem strongThinSeparatedCondExpr_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs e : ValExpr} {τ : CppType} :
    StrongThinSeparatedCondExpr Γ σ q rhs e τ →
    StrongThinSeparatedCondExpr (pushTypeScope Γ) (pushScope σ) q rhs e τ := by
  intro h
  induction h with
  | base hbase hty =>
      exact .base hbase (hasValueType_pushTypeScope hty)
  | loadDeref hw =>
      exact .loadDeref hw.pushScope
  | addrOfDeref hw =>
      exact .addrOfDeref hw.pushScope
  | add h1 h2 ih1 ih2 => exact .add ih1 ih2
  | sub h1 h2 ih1 ih2 => exact .sub ih1 ih2
  | mul h1 h2 ih1 ih2 => exact .mul ih1 ih2
  | eq h1 h2 ih1 ih2 => exact .eq ih1 ih2
  | lt h1 h2 ih1 ih2 => exact .lt ih1 ih2
  | not h ih => exact .not ih

mutual

theorem assign_head_transportable_decl_stmt_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} {st : CppStmt}
    (h : AssignHeadTransportableStmtDecl Γ σ q rhs st) :
    AssignHeadTransportableStmtDecl (pushTypeScope Γ) (pushScope σ) q rhs st := by
  match h with
  | .skip => exact .skip
  | .exprStmt hc hty =>
      exact .exprStmt (strongThinSeparatedCondExpr_pushScope hc) (hasValueType_pushTypeScope hty)
  | .assign hp hc hty =>
      exact .assign hp (strongThinSeparatedCondExpr_pushScope hc) (hasValueType_pushTypeScope hty)
  | .declareObjNone => exact .declareObjNone
  | .declareObjSome hc hty =>
      exact .declareObjSome (strongThinSeparatedCondExpr_pushScope hc) (hasValueType_pushTypeScope hty)
  | .declareRef hp => exact .declareRef hp
  | .seq hs ht =>
      exact .seq (assign_head_transportable_decl_stmt_pushScope hs) (assign_head_transportable_decl_stmt_pushScope ht)
  | .ite hc hs ht =>
      exact .ite (strongThinSeparatedCondExpr_pushScope hc)
                 (assign_head_transportable_decl_stmt_pushScope hs)
                 (assign_head_transportable_decl_stmt_pushScope ht)
  | .whileStmt hc hbody =>
      exact .whileStmt (strongThinSeparatedCondExpr_pushScope hc) (assign_head_transportable_decl_stmt_pushScope hbody)
  | .block hblock =>
      exact .block (assign_head_transportable_decl_block_pushScope hblock)
  | .breakStmt => exact .breakStmt
  | .continueStmt => exact .continueStmt
  | .returnNone => exact .returnNone
  | .returnSome hc hty =>
      exact .returnSome (strongThinSeparatedCondExpr_pushScope hc) (hasValueType_pushTypeScope hty)

theorem assign_head_transportable_decl_block_pushScope
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock}
    (h : AssignHeadTransportableBlockDecl Γ σ q rhs ss) :
    AssignHeadTransportableBlockDecl (pushTypeScope Γ) (pushScope σ) q rhs ss := by
  match h with
  | .nil => exact .nil
  | .cons hs hss =>
      exact .cons (assign_head_transportable_decl_stmt_pushScope hs) (assign_head_transportable_decl_block_pushScope hss)

end

/- =========================================================
   2. Replay across the fixed head assignment
   ========================================================= -/
mutual

theorem assign_head_transportable_decl_stmt_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {target : CppStmt}
    (htarget : AssignHeadTransportableStmtDecl Γ σ q rhs target) :
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ target →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' target := by
  intro hσ' hready hstep
  match htarget with
  | .skip => exact .skip
  | .exprStmt hc hty_hc =>
      match hready with
      | .exprStmt hty_ready heready =>
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact .exprStmt hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign hc hσ' heready hstep)
  | .assign hp hc hty_hc =>
      match hready with
      | .assign hpty hpready hvty_ready heready =>
          have heq := hasValueType_unique hvty_ready hty_hc
          subst heq
          exact .assign
            hpty
            (replay_stable_read_place_ready_after_assign hp hσ' hpready hstep)
            hvty_ready
            (strongThinSeparated_cond_expr_ready_after_assign hc hσ' heready hstep)
  | .declareObjNone =>
      match hready with
      | .declareObjNone hfresh hobj =>
          exact .declareObjNone hfresh hobj
  | .declareObjSome hc hty_hc =>
      match hready with
      | .declareObjSome hfresh hobj hty_ready heready =>
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact .declareObjSome
            hfresh hobj hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign hc hσ' heready hstep)
  | .declareRef hp =>
      match hready with
      | .declareRef hfresh hpty hpready =>
          exact .declareRef
            hfresh hpty
            (replay_stable_read_place_ready_after_assign hp hσ' hpready hstep)
  | .seq hs ht =>
      match hready with
      | .seq hreadyS hreadyT =>
          exact .seq
            (assign_head_transportable_decl_stmt_ready_after_assign_head hs hσ' hreadyS hstep)
            (assign_head_transportable_decl_stmt_ready_after_assign_head ht hσ' hreadyT hstep)
  | .ite hc hs ht =>
      match hready with
      | .ite hcty hcready hreadyS hreadyT =>
          exact .ite
            hcty
            (strongThinSeparated_cond_expr_ready_after_assign hc hσ' hcready hstep)
            (assign_head_transportable_decl_stmt_ready_after_assign_head hs hσ' hreadyS hstep)
            (assign_head_transportable_decl_stmt_ready_after_assign_head ht hσ' hreadyT hstep)
  | .whileStmt hc hbody =>
      match hready with
      | .whileStmt hcty hcready hreadyBody =>
          exact .whileStmt
            hcty
            (strongThinSeparated_cond_expr_ready_after_assign hc hσ' hcready hstep)
            (assign_head_transportable_decl_stmt_ready_after_assign_head hbody hσ' hreadyBody hstep)
  | .block hblock =>
      match hready with
      | .block hreadyBlock =>
          have hσ'Push : ScopedTypedStateConcrete (pushTypeScope Γ) (pushScope σ') :=
            scoped_typed_state_concrete_pushScope hσ'
          have hstepPush : BigStepStmt (pushScope σ) (.assign q rhs) .normal (pushScope σ') :=
            bigStepStmt_assign_pushScope hstep
          exact .block
            (assign_head_transportable_decl_block_ready_after_assign_head hblock hσ'Push hreadyBlock hstepPush)
  | .breakStmt => exact .breakStmt
  | .continueStmt => exact .continueStmt
  | .returnNone => exact .returnNone
  | .returnSome hc hty_hc =>
      match hready with
      | .returnSome hty_ready heready =>
          have heq := hasValueType_unique hty_ready hty_hc
          subst heq
          exact .returnSome
            hty_ready
            (strongThinSeparated_cond_expr_ready_after_assign hc hσ' heready hstep)

theorem assign_head_transportable_decl_block_ready_after_assign_head
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock}
    (hblock : AssignHeadTransportableBlockDecl Γ σ q rhs ss) :
    ScopedTypedStateConcrete Γ σ' →
    BlockReadyConcrete Γ σ ss →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BlockReadyConcrete Γ σ' ss := by
  intro hσ' hready hstep
  match hblock with
  | .nil => exact .nil
  | .cons hs hss =>
      match hready with
      | .cons hreadyS hreadySS =>
          exact .cons
            (assign_head_transportable_decl_stmt_ready_after_assign_head hs hσ' hreadyS hstep)
            (assign_head_transportable_decl_block_ready_after_assign_head hss hσ' hreadySS hstep)

end

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
  have hΘ : Θ = Γ := by exact assign_stmt_env_preserving htyHead
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
  have hΞ : Ξ = Γ := by exact assign_stmt_env_preserving htyHead
  subst hΞ
  have hσ'Γ : ScopedTypedStateConcrete Ξ σ' :=
    assign_stmt_normal_preserves_scoped_typed_state_concrete
      htyHead hσ (cons_block_ready_head hready) hstep
  have hreadyTail' : BlockReadyConcrete Ξ σ' ss :=
    assign_head_transportable_decl_block_ready_after_assign_head
      htail hσ'Γ (cons_block_ready_tail_declfrag hready) hstep
  exact ⟨Ξ, htyTail, hσ'Γ, hreadyTail'⟩

end Cpp
