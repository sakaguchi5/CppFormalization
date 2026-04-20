import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
A declaration-extended residual fragment on top of the bundled assign transport
kernel.

Compared to the earlier stable fragment, this file adds the declaration cases
that are *not* the real frontier:

- `declareObj τ x none`
- `declareObj τ x (some e)` when the initializer is already in the replay-stable
  expression fragment
- `declareRef τ x p` when the referenced place is in the replay-stable
  read-place fragment

This is the honest next step: declaration suffixes are largely about freshness
and environment preservation, not about the deep alias-sensitive gap.
-/

theorem replay_stable_primitive_stmt_is_primitive_normal_declfrag
    {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    (match st with
     | .skip => True
     | .exprStmt _ => True
     | .assign _ _ => True
     | .declareObj _ _ _ => True
     | .declareRef _ _ _ => True
     | .breakStmt => False
     | .continueStmt => False
     | .returnStmt _ => False
     | .seq _ _ => False
     | .ite _ _ _ => False
     | .whileStmt _ _ => False
     | .block _ => False) := by
  intro h
  cases st <;> simp [ReplayStablePrimitiveStmt] at h ⊢

theorem seq_ready_right_declfrag
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.seq s t) →
    StmtReadyConcrete Γ σ t := by
  intro h
  cases h with
  | seq _ ht =>
      exact ht

theorem cons_block_ready_tail_declfrag
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ (.cons s ss) →
    BlockReadyConcrete Γ σ ss := by
  intro h
  cases h with
  | cons _ htail =>
      exact htail

theorem replay_stable_read_place_ready_after_replay_stable_primitive_declfrag
    {Γ : TypeEnv} {σ σ' : State}
    {head : CppStmt} {p : PlaceExpr} {τ : CppType} :
    ReplayStablePrimitiveStmt head →
    ReplayStableReadPlace p →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ p τ →
    BigStepStmt σ head .normal σ' →
    PlaceReadyConcrete Γ σ' p τ := by
  intro hhead hpstable hσ' hpready hstep
  cases head <;> simp [ReplayStablePrimitiveStmt] at hhead
  case skip =>
    exact replay_stable_read_place_ready_after_skip hpstable hpready hstep
  case exprStmt e =>
    exact replay_stable_read_place_ready_after_exprStmt hpstable hpready hstep
  case assign q e =>
    exact replay_stable_read_place_ready_after_assign hpstable hσ' hpready hstep

inductive ReplayTransportableStmtDecl : CppStmt → Prop where
  | skip :
      ReplayTransportableStmtDecl .skip
  | exprStmt {e : ValExpr} :
      ReplayStableCondExpr e →
      ReplayTransportableStmtDecl (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} :
      ReplayStableReadPlace p →
      ReplayStableCondExpr e →
      ReplayTransportableStmtDecl (.assign p e)
  | declareObjNone {τ : CppType} {x : Ident} :
      ReplayTransportableStmtDecl (.declareObj τ x none)
  | declareObjSome {τ : CppType} {x : Ident} {e : ValExpr} :
      ReplayStableCondExpr e →
      ReplayTransportableStmtDecl (.declareObj τ x (some e))
  | declareRef {τ : CppType} {x : Ident} {p : PlaceExpr} :
      ReplayStableReadPlace p →
      ReplayTransportableStmtDecl (.declareRef τ x p)
  | seq {s t : CppStmt} :
      ReplayTransportableStmtDecl s →
      ReplayTransportableStmtDecl t →
      ReplayTransportableStmtDecl (.seq s t)
  | ite {c : ValExpr} {s t : CppStmt} :
      ReplayStableCondExpr c →
      ReplayTransportableStmtDecl s →
      ReplayTransportableStmtDecl t →
      ReplayTransportableStmtDecl (.ite c s t)
  | whileStmt {c : ValExpr} {body : CppStmt} :
      ReplayStableCondExpr c →
      ReplayTransportableStmtDecl body →
      ReplayTransportableStmtDecl (.whileStmt c body)
  | breakStmt :
      ReplayTransportableStmtDecl .breakStmt
  | continueStmt :
      ReplayTransportableStmtDecl .continueStmt
  | returnNone :
      ReplayTransportableStmtDecl (.returnStmt none)
  | returnSome {e : ValExpr} :
      ReplayStableCondExpr e →
      ReplayTransportableStmtDecl (.returnStmt (some e))

inductive ReplayTransportableBlockDecl : StmtBlock → Prop where
  | nil :
      ReplayTransportableBlockDecl .nil
  | cons {s : CppStmt} {ss : StmtBlock} :
      ReplayTransportableStmtDecl s →
      ReplayTransportableBlockDecl ss →
      ReplayTransportableBlockDecl (.cons s ss)

theorem replay_transportable_decl_stmt_ready_after_replay_stable_primitive_head
    {Γ : TypeEnv} {σ σ' : State}
    {head target : CppStmt} :
    ReplayStablePrimitiveStmt head →
    ReplayTransportableStmtDecl target →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ target →
    BigStepStmt σ head .normal σ' →
    StmtReadyConcrete Γ σ' target := by
  intro hhead htarget hσ' hready hstep
  induction htarget generalizing Γ σ σ' with
  | skip =>
      exact StmtReadyConcrete.skip
  | exprStmt hc =>
      cases hready with
      | exprStmt hty heready =>
          exact StmtReadyConcrete.exprStmt hty
            (replay_stable_cond_expr_ready_after_replay_stable_primitive
              hhead hc hσ' heready hstep)
  | assign hp hc =>
      cases hready with
      | assign hpty hpready hvty heready =>
          exact StmtReadyConcrete.assign
            hpty
            (replay_stable_read_place_ready_after_replay_stable_primitive_declfrag
              hhead hp hσ' hpready hstep)
            hvty
            (replay_stable_cond_expr_ready_after_replay_stable_primitive
              hhead hc hσ' heready hstep)
  | declareObjNone =>
      cases hready with
      | declareObjNone hfresh hobj =>
          exact StmtReadyConcrete.declareObjNone hfresh hobj
  | declareObjSome hc =>
      cases hready with
      | declareObjSome hfresh hobj hty heready =>
          exact StmtReadyConcrete.declareObjSome
            hfresh hobj hty
            (replay_stable_cond_expr_ready_after_replay_stable_primitive
              hhead hc hσ' heready hstep)
  | declareRef hp =>
      cases hready with
      | declareRef hfresh hpty hpready =>
          exact StmtReadyConcrete.declareRef
            hfresh hpty
            (replay_stable_read_place_ready_after_replay_stable_primitive_declfrag
              hhead hp hσ' hpready hstep)
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
            (replay_stable_cond_expr_ready_after_replay_stable_primitive
              hhead hc hσ' hcready hstep)
            (ihS hσ' hreadyS hstep)
            (ihT hσ' hreadyT hstep)
  | whileStmt hc hbody ihBody =>
      cases hready with
      | whileStmt hcty hcready hreadyBody =>
          exact StmtReadyConcrete.whileStmt
            hcty
            (replay_stable_cond_expr_ready_after_replay_stable_primitive
              hhead hc hσ' hcready hstep)
            (ihBody hσ' hreadyBody hstep)
  | breakStmt =>
      exact StmtReadyConcrete.breakStmt
  | continueStmt =>
      exact StmtReadyConcrete.continueStmt
  | returnNone =>
      exact StmtReadyConcrete.returnNone
  | returnSome hc =>
      cases hready with
      | returnSome hty heready =>
          exact StmtReadyConcrete.returnSome
            hty
            (replay_stable_cond_expr_ready_after_replay_stable_primitive
              hhead hc hσ' heready hstep)

theorem replay_transportable_decl_block_ready_after_replay_stable_primitive_head
    {Γ : TypeEnv} {σ σ' : State}
    {head : CppStmt} {ss : StmtBlock} :
    ReplayStablePrimitiveStmt head →
    ReplayTransportableBlockDecl ss →
    ScopedTypedStateConcrete Γ σ' →
    BlockReadyConcrete Γ σ ss →
    BigStepStmt σ head .normal σ' →
    BlockReadyConcrete Γ σ' ss := by
  intro hhead hblock hσ' hready hstep
  induction hblock generalizing Γ σ σ' with
  | nil =>
      exact BlockReadyConcrete.nil
  | cons hs hss ih =>
      cases hready with
      | cons hreadyS hreadySS =>
          exact BlockReadyConcrete.cons
            (replay_transportable_decl_stmt_ready_after_replay_stable_primitive_head
              hhead hs hσ' hreadyS hstep)
            (ih hσ' hreadySS hstep)

theorem replay_transportable_decl_right_seq_normal_preserves_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    ReplayStablePrimitiveStmt s →
    ReplayTransportableStmtDecl t →
    HasTypeStmtCI .normalK Γ (.seq s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    BigStepStmt σ s .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro hleft hright htySeq hσ hreadySeq hstepLeft
  rcases seq_typing_data htySeq with ⟨Θ, htyLeft, htyRight⟩
  have hΘ : Θ = Γ := by
    exact replay_stable_primitive_stmt_env_preserving hleft htyLeft
  subst hΘ
  let hprim := replay_stable_primitive_stmt_is_primitive_normal_declfrag hleft
  have hσ'Γ : ScopedTypedStateConcrete Θ σ' :=
    primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim htyLeft hσ (seq_ready_left hreadySeq) hstepLeft
  have hreadyRight' : StmtReadyConcrete Θ σ' t :=
    replay_transportable_decl_stmt_ready_after_replay_stable_primitive_head
      hleft hright hσ'Γ (seq_ready_right_declfrag hreadySeq) hstepLeft
  exact ⟨Θ, htyRight, hσ'Γ, hreadyRight'⟩

theorem replay_transportable_decl_tail_cons_head_normal_preserves_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    ReplayStablePrimitiveStmt s →
    ReplayTransportableBlockDecl ss →
    HasTypeBlockCI .normalK Γ (.cons s ss) Θ →
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    ConsResidualBoundary Θ σ' ss := by
  intro hhead htail hty hσ hready hstep
  rcases cons_block_typing_data hty with ⟨Ξ, htyHead, htyTail⟩
  have hΞ : Ξ = Γ := by
    exact replay_stable_primitive_stmt_env_preserving hhead htyHead
  subst hΞ
  let hprim := replay_stable_primitive_stmt_is_primitive_normal_declfrag hhead
  have hσ'Γ : ScopedTypedStateConcrete Ξ σ' :=
    primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim htyHead hσ (cons_block_ready_head hready) hstep
  have hreadyTail' : BlockReadyConcrete Ξ σ' ss :=
    replay_transportable_decl_block_ready_after_replay_stable_primitive_head
      hhead htail hσ'Γ (cons_block_ready_tail_declfrag hready) hstep
  exact ⟨Ξ, htyTail, hσ'Γ, hreadyTail'⟩

end Cpp
