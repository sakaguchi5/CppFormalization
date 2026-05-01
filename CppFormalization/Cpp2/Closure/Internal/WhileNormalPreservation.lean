import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.ReadinessReplayPrimitive
import CppFormalization.Cpp2.Closure.Internal.ConditionReplayKernel
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI
import CppFormalization.Cpp2.Closure.Internal.StrongThinSeparatedCondReplay
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.WhileReentryKernelFacts

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
   1. generic theorem from body/tail subproofs, now via reentry kernel
   ========================================================= -/

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

end Cpp
