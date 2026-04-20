import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
A theoremized residual fragment on top of the new bundled assign transport kernel.

This file does **not** claim the full residual-readiness axioms.
Instead, it isolates an honest suffix fragment whose readiness can already be
transported across replay-stable primitive heads (`skip / exprStmt / assign`).

The point is strategic:
- keep the general residual axioms in place for now;
- nevertheless convert a mathematically natural and C++-honest fragment from
  axiom land into theorem land;
- make explicit where the remaining gap really is.
-/

theorem replay_stable_primitive_stmt_is_primitive_normal_local
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

theorem seq_ready_right
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.seq s t) →
    StmtReadyConcrete Γ σ t := by
  intro h
  cases h with
  | seq _ ht =>
      exact ht

theorem cons_block_ready_tail
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock} :
    BlockReadyConcrete Γ σ (.cons s ss) →
    BlockReadyConcrete Γ σ ss := by
  intro h
  cases h with
  | cons _ htail =>
      exact htail

theorem replay_stable_read_place_ready_after_replay_stable_primitive
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

inductive ReplayTransportableStmt : CppStmt → Prop where
  | skip :
      ReplayTransportableStmt .skip
  | exprStmt {e : ValExpr} :
      ReplayStableCondExpr e →
      ReplayTransportableStmt (.exprStmt e)
  | assign {p : PlaceExpr} {e : ValExpr} :
      ReplayStableReadPlace p →
      ReplayStableCondExpr e →
      ReplayTransportableStmt (.assign p e)
  | seq {s t : CppStmt} :
      ReplayTransportableStmt s →
      ReplayTransportableStmt t →
      ReplayTransportableStmt (.seq s t)
  | ite {c : ValExpr} {s t : CppStmt} :
      ReplayStableCondExpr c →
      ReplayTransportableStmt s →
      ReplayTransportableStmt t →
      ReplayTransportableStmt (.ite c s t)
  | whileStmt {c : ValExpr} {body : CppStmt} :
      ReplayStableCondExpr c →
      ReplayTransportableStmt body →
      ReplayTransportableStmt (.whileStmt c body)
  | breakStmt :
      ReplayTransportableStmt .breakStmt
  | continueStmt :
      ReplayTransportableStmt .continueStmt
  | returnNone :
      ReplayTransportableStmt (.returnStmt none)
  | returnSome {e : ValExpr} :
      ReplayStableCondExpr e →
      ReplayTransportableStmt (.returnStmt (some e))

inductive ReplayTransportableBlock : StmtBlock → Prop where
  | nil :
      ReplayTransportableBlock .nil
  | cons {s : CppStmt} {ss : StmtBlock} :
      ReplayTransportableStmt s →
      ReplayTransportableBlock ss →
      ReplayTransportableBlock (.cons s ss)

theorem replay_transportable_stmt_ready_after_replay_stable_primitive_head
    {Γ : TypeEnv} {σ σ' : State}
    {head target : CppStmt} :
    ReplayStablePrimitiveStmt head →
    ReplayTransportableStmt target →
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
            (replay_stable_read_place_ready_after_replay_stable_primitive
              hhead hp hσ' hpready hstep)
            hvty
            (replay_stable_cond_expr_ready_after_replay_stable_primitive
              hhead hc hσ' heready hstep)
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

theorem replay_transportable_block_ready_after_replay_stable_primitive_head
    {Γ : TypeEnv} {σ σ' : State}
    {head : CppStmt} {ss : StmtBlock} :
    ReplayStablePrimitiveStmt head →
    ReplayTransportableBlock ss →
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
            (replay_transportable_stmt_ready_after_replay_stable_primitive_head
              hhead hs hσ' hreadyS hstep)
            (ih hσ' hreadySS hstep)

theorem replay_transportable_right_seq_normal_preserves_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt} :
    ReplayStablePrimitiveStmt s →
    ReplayTransportableStmt t →
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
  let hprim := replay_stable_primitive_stmt_is_primitive_normal_local hleft

  have hσ'Γ : ScopedTypedStateConcrete Θ σ' :=
    primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim htyLeft hσ (seq_ready_left hreadySeq) hstepLeft
  have hreadyRight' : StmtReadyConcrete Θ σ' t :=
    replay_transportable_stmt_ready_after_replay_stable_primitive_head
      hleft hright hσ'Γ (seq_ready_right hreadySeq) hstepLeft
  exact ⟨Θ, htyRight, hσ'Γ, hreadyRight'⟩

theorem replay_transportable_tail_cons_head_normal_preserves_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock} :
    ReplayStablePrimitiveStmt s →
    ReplayTransportableBlock ss →
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
  let hprim := replay_stable_primitive_stmt_is_primitive_normal_local hhead
  have hσ'Ξ : ScopedTypedStateConcrete Ξ σ' :=
    primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim htyHead hσ (cons_block_ready_head hready) hstep
  have hreadyTail' : BlockReadyConcrete Ξ σ' ss :=
    replay_transportable_block_ready_after_replay_stable_primitive_head
      hhead htail hσ'Ξ (cons_block_ready_tail hready) hstep
  exact ⟨Ξ, htyTail, hσ'Ξ, hreadyTail'⟩

end Cpp
