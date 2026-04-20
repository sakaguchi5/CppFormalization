import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI
import CppFormalization.Cpp2.Closure.Internal.StrongThinSeparatedCondReplay

namespace Cpp

/-!
# Closure.Internal.WhileNormalPreservation

`while` の normal-path preservation を、`LoopBodyBoundaryCI` と
`LoopReentryKernelCI` を明示した形へ組み替える。

重要:
- loop body の local 4-channel contract は `LoopBodyBoundaryCI` が担う。
- body の `normal` / `continue` 後に header へ再入できることは
  `LoopReentryKernelCI` が担う。
- したがって旧 generic axiom
  `while_ready_after_body_normal` / `while_ready_after_body_continue`
  にはもう依存しない。
-/

/- =========================================================
   1. typing / readiness / operational 分解
   ========================================================= -/

theorem while_typing_data
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    Δ = Γ ∧
    HasValueType Γ c (.base .bool) ∧
    HasTypeStmtCI .normalK Γ body Γ ∧
    HasTypeStmtCI .breakK Γ body Γ ∧
    HasTypeStmtCI .continueK Γ body Γ := by
  intro h
  exact while_normal_typing_data h

theorem while_ready_body_data
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    StmtReadyConcrete Γ σ body := by
  intro h
  cases h with
  | whileStmt _ _ hbody =>
      simpa using hbody

theorem while_ready_cond_data
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    HasValueType Γ c (.base .bool) ∧ ExprReadyConcrete Γ σ c (.base .bool) := by
  intro h
  cases h with
  | whileStmt hc hcr _ =>
      exact ⟨hc, hcr⟩

theorem while_normal_data
    {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    BigStepStmt σ (.whileStmt c body) .normal σ' →
      (σ' = σ) ∨
      (∃ σ1,
        BigStepStmt σ body .normal σ1 ∧
        BigStepStmt σ1 (.whileStmt c body) .normal σ') ∨
      (∃ σ1,
        BigStepStmt σ body .breakResult σ1 ∧
        σ' = σ1) ∨
      (∃ σ1,
        BigStepStmt σ body .continueResult σ1 ∧
        BigStepStmt σ1 (.whileStmt c body) .normal σ') := by
  intro h
  cases h with
  | whileFalse _ =>
      exact Or.inl rfl
  | whileTrueNormal _ hBody hTail =>
      exact Or.inr (Or.inl ⟨_, hBody, hTail⟩)
  | whileTrueBreak _ hBody =>
      exact Or.inr (Or.inr (Or.inl ⟨_, hBody, rfl⟩))
  | whileTrueContinue _ hBody hTail =>
      exact Or.inr (Or.inr (Or.inr ⟨_, hBody, hTail⟩))

/- =========================================================
   2. generic theorem from body/tail subproofs, now via reentry kernel
   ========================================================= -/

def WhileTailClosed
    (Γ : TypeEnv) (σ' : State) (c : ValExpr) (body : CppStmt) : Prop :=
  ∀ {σ1},
    ScopedTypedStateConcrete Γ σ1 →
    StmtReadyConcrete Γ σ1 (.whileStmt c body) →
    BigStepStmt σ1 (.whileStmt c body) .normal σ' →
    ScopedTypedStateConcrete Γ σ'

theorem while_normal_stop_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    σ' = σ →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hEq
  rcases while_typing_data hty with ⟨hΔ, _, _, _, _⟩
  subst hΔ
  subst hEq
  exact hσ

theorem while_ready_after_body_normal_via_reentry
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_normal hcond hbody hstep

theorem while_ready_after_body_continue_via_reentry
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_continue hcond hbody hstep
--旧axiomの移行用補題
theorem while_ready_after_body_normal_of_kernel
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_normal hcond hbody hstep

theorem while_ready_after_body_continue_of_kernel
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_continue hcond hbody hstep
  --
theorem while_normal_body_normal_case_preserves_scoped_typed_state_via_reentry
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    (∀ {σ1},
      BigStepStmt σ body .normal σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    (∃ σ1,
      BigStepStmt σ body .normal σ1 ∧
      BigStepStmt σ1 (.whileStmt c body) .normal σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hcond hbody K hbodyNorm htail hcase
  rcases while_typing_data hty with ⟨hΔ, _, _, _, _⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, htailStep⟩
  have hσ1 := hbodyNorm hbodyStep
  have hreadyTail := K.whileReady_after_normal hcond hbody hbodyStep
  exact htail hσ1 hreadyTail htailStep

theorem while_normal_body_break_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    LoopBodyBoundaryCI Γ σ body →
    (∀ {σ1},
      BigStepStmt σ body .breakResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    (∃ σ1,
      BigStepStmt σ body .breakResult σ1 ∧
      σ' = σ1) →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hbody hbodyBreak hcase
  rcases while_typing_data hty with ⟨hΔ, _, _, _, _⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, hEq⟩
  have hσ1 := hbodyBreak hbodyStep
  subst hEq
  exact hσ1

theorem while_normal_body_continue_case_preserves_scoped_typed_state_via_reentry
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    (∀ {σ1},
      BigStepStmt σ body .continueResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    (∃ σ1,
      BigStepStmt σ body .continueResult σ1 ∧
      BigStepStmt σ1 (.whileStmt c body) .normal σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hcond hbody K hbodyCont htail hcase
  rcases while_typing_data hty with ⟨hΔ, _, _, _, _⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, htailStep⟩
  have hσ1 := hbodyCont hbodyStep
  have hreadyTail := K.whileReady_after_continue hcond hbody hbodyStep
  exact htail hσ1 hreadyTail htailStep

theorem while_normal_preserves_scoped_typed_state_from_loop_boundary_and_tail
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    ExprReadyConcrete Γ σ c (.base .bool) →
    LoopBodyBoundaryCI Γ σ body →
    LoopReentryKernelCI Γ c body →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    (∀ {σ1},
      BigStepStmt σ body .normal σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    (∀ {σ1},
      BigStepStmt σ body .breakResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    (∀ {σ1},
      BigStepStmt σ body .continueResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hcond hbody K hstep hbodyNorm hbodyBreak hbodyCont htail
  rcases while_normal_data hstep with hstop | hnorm | hbreak | hcont
  · exact while_normal_stop_case_preserves_scoped_typed_state hty hσ hstop
  · exact while_normal_body_normal_case_preserves_scoped_typed_state_via_reentry
      hty hσ hcond hbody K hbodyNorm htail hnorm
  · exact while_normal_body_break_case_preserves_scoped_typed_state
      hty hσ hbody hbodyBreak hbreak
  · exact while_normal_body_continue_case_preserves_scoped_typed_state_via_reentry
      hty hσ hcond hbody K hbodyCont htail hcont

/- =========================================================
   3. primitive body の corollary
   ========================================================= -/

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

/- =========================================================
   4. replay-stable primitive case remains useful as a concrete reentry target
   ========================================================= -/

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

/--
This theorem is now best read as the core ingredient for constructing a
concrete `LoopReentryKernelCI` instance for replay-stable primitive bodies.
-/
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
  rcases while_typing_data htyWhile with ⟨_, hc, hN, _, _⟩
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

theorem while_ready_after_body_normal_of_strongThinSeparated_assign
    {Γ : TypeEnv} {σ σ' : State}
    {c q : PlaceExpr} {rhs : ValExpr} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.assign q rhs)) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c (.assign q rhs)) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c (.assign q rhs)) := by
  intro hc htyWhile hσ' hreadyWhile hstepBody
  have hreadyBody : StmtReadyConcrete Γ σ (.assign q rhs) :=
    while_ready_body_data hreadyWhile
  have hreadyBody' : StmtReadyConcrete Γ σ' (.assign q rhs) :=
    assign_stmt_ready_replay_concrete hσ' hreadyBody hstepBody
  have hcondReady0 : ExprReadyConcrete Γ σ c (.base .bool) :=
    (while_ready_cond_data hreadyWhile).2
  have hcondReady' : ExprReadyConcrete Γ σ' c (.base .bool) :=
    strongThinSeparated_cond_expr_ready_after_assign hc hσ' hcondReady0 hstepBody
  rcases while_typing_data htyWhile with ⟨_, hcb, _, _, _⟩
  exact StmtReadyConcrete.whileStmt hcb hcondReady' hreadyBody'

theorem while_ready_after_body_continue_of_strongThinSeparated_assign
    {Γ : TypeEnv} {σ σ' : State}
    {c : ValExpr} {q : PlaceExpr} {rhs : ValExpr} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.assign q rhs)) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c (.assign q rhs)) →
    BigStepStmt σ (.assign q rhs) .continueResult σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c (.assign q rhs)) := by
  intro _ _ _ _ hstepBody
  cases hstepBody

theorem strongThinSeparated_assign_body_while_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State}
    {c : ValExpr} {q : PlaceExpr} {rhs : ValExpr} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.assign q rhs)) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c (.assign q rhs)) →
    BigStepStmt σ (.whileStmt c (.assign q rhs)) .normal σ' →
    WhileTailClosed Γ σ' c (.assign q rhs) →
    ScopedTypedStateConcrete Δ σ' := by
  intro hc htyWhile hσ hready hstep htail
  rcases while_typing_data htyWhile with ⟨hΔ, _, hN, _, _⟩
  subst hΔ
  rcases while_normal_data hstep with hstop | hnorm | hbreak | hcont
  · subst hstop
    exact hσ
  · rcases hnorm with ⟨σ1, hbodyStep, htailStep⟩
    have hreadyBody : StmtReadyConcrete Γ σ (.assign q rhs) :=
      while_ready_body_data hready
    have hσ1 : ScopedTypedStateConcrete Γ σ1 :=
      assign_stmt_normal_preserves_scoped_typed_state_concrete
        hN hσ hreadyBody hbodyStep
    have hreadyTail : StmtReadyConcrete Γ σ1 (.whileStmt c (.assign q rhs)) :=
      while_ready_after_body_normal_of_strongThinSeparated_assign
        hc htyWhile hσ1 hready hbodyStep
    exact htail hσ1 hreadyTail htailStep
  · rcases hbreak with ⟨_, hbodyStep, _⟩
    cases hbodyStep
  · rcases hcont with ⟨_, hbodyStep, _⟩
    cases hbodyStep

end Cpp
