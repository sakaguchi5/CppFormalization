import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReentryKernelFacts
import CppFormalization.Cpp2.Closure.Internal.WhileNormalPreservation

namespace Cpp

theorem primitive_normal_stmt_no_break
    {σ σ' : State} {st : CppStmt} :
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
     | .block _ => False) →
    ¬ BigStepStmt σ st .breakResult σ' := by
  intro hprim hbreak
  cases st <;> simp at hprim <;> cases hbreak

theorem primitive_normal_stmt_no_continue
    {σ σ' : State} {st : CppStmt} :
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
     | .block _ => False) →
    ¬ BigStepStmt σ st .continueResult σ' := by
  intro hprim hcont
  cases st <;> simp at hprim <;> cases hcont

theorem primitive_body_while_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    (match body with
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
     | .block _ => False) →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    (∀ {σ1},
      ScopedTypedStateConcrete Γ σ1 →
      StmtReadyConcrete Γ σ1 (.whileStmt c body) →
      BigStepStmt σ1 (.whileStmt c body) .normal σ' →
      ScopedTypedStateConcrete Γ σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hcond hbody K hstep htail
  rcases while_typing_data hty with ⟨_, _, hbodyTy, _, _⟩
  refine while_normal_preserves_scoped_typed_state_from_loop_boundary_and_tail
    hty hσ hcond hbody K hstep ?_ ?_ ?_ ?_
  · intro σ1 hbodyStep
    exact primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim hbodyTy hσ hbody.dynamic.safe hbodyStep
  · intro σ1 hbodyStep
    exfalso
    exact primitive_normal_stmt_no_break hprim hbodyStep
  · intro σ1 hbodyStep
    exfalso
    exact primitive_normal_stmt_no_continue hprim hbodyStep
  · intro σ1 hσ1 hreadyTail htailStep
    exact htail hσ1 hreadyTail htailStep

theorem while_normal_preserves_scoped_typed_state_concrete_of_primitive_body
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    (match body with
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
     | .block _ => False) →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hcond hbody K hstep htail
  exact primitive_body_while_normal_preserves_scoped_typed_state_concrete
    hprim hty hσ hcond hbody K hstep htail

theorem replay_stable_primitive_stmt_is_primitive_normal
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

theorem replay_stable_primitive_stmt_no_break
    {σ σ' : State} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    ¬ BigStepStmt σ st .breakResult σ' := by
  intro hstable hbreak
  cases st <;>
    simp [ReplayStablePrimitiveStmt] at hstable <;>
    cases hbreak

theorem replay_stable_primitive_stmt_no_continue
    {σ σ' : State} {st : CppStmt} :
    ReplayStablePrimitiveStmt st →
    ¬ BigStepStmt σ st .continueResult σ' := by
  intro hstable hcont
  cases st <;>
    simp [ReplayStablePrimitiveStmt] at hstable <;>
    cases hcont

theorem while_ready_after_body_normal_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hstable hcstable htyWhile hσ' hreadyWhile hstepBody
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hreadyWhile
  have hreadyBody' : StmtReadyConcrete Γ σ' body :=
    replay_stable_primitive_stmt_ready_replay_concrete
      hstable hσ' hreadyBody hstepBody
  have hcondReady0 : ExprReadyConcrete Γ σ c (.base .bool) :=
    (while_ready_cond_data hreadyWhile).2
  have hcondReady' : ExprReadyConcrete Γ σ' c (.base .bool) :=
    replay_stable_cond_expr_ready_after_replay_stable_primitive
      hstable hcstable hσ' hcondReady0 hstepBody
  rcases while_typing_data htyWhile with ⟨_, hc, _, _, _⟩
  exact StmtReadyConcrete.whileStmt hc hcondReady' hreadyBody'

theorem while_ready_after_body_continue_of_replay_stable_primitive
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hstable _ _ _ _ hstepBody
  have hfalse : False := replay_stable_primitive_stmt_no_continue hstable hstepBody
  exact False.elim hfalse

theorem replay_stable_primitive_body_while_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    ReplayStablePrimitiveStmt body →
    ReplayStableCondExpr c →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hstable hcstable htyWhile hσ hready hstep htail
  rcases while_typing_data htyWhile with ⟨hΔ, _, hN, _, _⟩
  subst hΔ
  rcases while_normal_data hstep with hstop | hnorm | hbreak | hcont
  · subst hstop
    exact hσ
  · rcases hnorm with ⟨σ1, hbodyStep, htailStep⟩
    have hreadyBody : StmtReadyConcrete Δ σ body :=
      while_ready_body_data hready
    have hprim := replay_stable_primitive_stmt_is_primitive_normal hstable
    have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
      primitive_stmt_normal_preserves_scoped_typed_state_concrete
        hprim hN hσ hreadyBody hbodyStep
    have hreadyTail : StmtReadyConcrete Δ σ1 (.whileStmt c body) :=
      while_ready_after_body_normal_of_replay_stable_primitive
        hstable hcstable htyWhile hσ1 hready hbodyStep
    exact htail hσ1 hreadyTail htailStep
  · rcases hbreak with ⟨σ1, hbodyStep, _⟩
    have hfalse : False := replay_stable_primitive_stmt_no_break hstable hbodyStep
    exact False.elim hfalse
  · rcases hcont with ⟨σ1, hbodyStep, _⟩
    have hfalse : False := replay_stable_primitive_stmt_no_continue hstable hbodyStep
    exact False.elim hfalse

end Cpp
