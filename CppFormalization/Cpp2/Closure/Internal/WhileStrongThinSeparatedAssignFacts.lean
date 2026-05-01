import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.StrongThinSeparatedCondReplay
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReentryKernelFacts

namespace Cpp

/-!
# Closure.Internal.WhileStrongThinSeparatedAssignFacts

Legacy weak `while` facts for the special body `.assign q rhs` under a
strong-thin-separated condition witness.

These facts are intentionally kept separate from
`WhileNormalPreservation.lean`, which now focuses on the generic
loop-boundary + reentry-kernel preservation theorem.
-/

theorem while_ready_after_body_normal_of_strongThinSeparated_assign
    {Γ : TypeEnv} {σ σ' : State}
    {c : ValExpr} {q : PlaceExpr} {rhs : ValExpr} :
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
    have hreadyBody : StmtReadyConcrete Δ σ (.assign q rhs) :=
      while_ready_body_data hready
    have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
      assign_stmt_normal_preserves_scoped_typed_state_concrete
        hN hσ hreadyBody hbodyStep
    have hreadyTail : StmtReadyConcrete Δ σ1 (.whileStmt c (.assign q rhs)) :=
      while_ready_after_body_normal_of_strongThinSeparated_assign
        hc htyWhile hσ1 hready hbodyStep
    exact htail hσ1 hreadyTail htailStep
  · rcases hbreak with ⟨_, hbodyStep, _⟩
    cases hbodyStep
  · rcases hcont with ⟨_, hbodyStep, _⟩
    cases hbodyStep

end Cpp
