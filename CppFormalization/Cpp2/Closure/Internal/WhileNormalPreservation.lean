import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
`while` の normal-path preservation。

ここで直接示したいのは
`BigStepStmt σ (.whileStmt c body) .normal σ'`
なら `ScopedTypedStateConcrete Γ σ'`
が保たれることだが、その本体は

1. 条件が false で即 normal 終了する場合
2. body が normal で 1 周進んでから tail loop が normal 終了する場合
3. body が continue で 1 周進んでから tail loop が normal 終了する場合

の 3 分岐である。

このファイルでは generic な while 分解を axiomatize し、
primitive body の場合の corollary を theorem として束ねる。
-/

/- =========================================================
   1. typing / readiness / operational 分解
   ========================================================= -/

axiom while_typing_data
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    Δ = Γ ∧ HasTypeStmtCI .normalK Γ body Γ

axiom while_ready_body_data
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    StmtReadyConcrete Γ σ body

axiom while_ready_after_body_normal
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ body Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body)

axiom while_ready_after_body_continue
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ body Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ body .continueResult σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body)

axiom while_normal_data
    {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    BigStepStmt σ (.whileStmt c body) .normal σ' →
      (σ' = σ) ∨
      (∃ σ1,
        BigStepStmt σ body .normal σ1 ∧
        BigStepStmt σ1 (.whileStmt c body) .normal σ') ∨
      (∃ σ1,
        BigStepStmt σ body .continueResult σ1 ∧
        BigStepStmt σ1 (.whileStmt c body) .normal σ')


/- =========================================================
   2. generic theorem from body/tail subproofs
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
  rcases while_typing_data hty with ⟨hΔ, hbodyTy⟩
  subst hΔ
  subst hEq
  exact hσ


theorem while_normal_body_normal_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .normal σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    (∃ σ1,
      BigStepStmt σ body .normal σ1 ∧
      BigStepStmt σ1 (.whileStmt c body) .normal σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hbodyNorm htail hcase
  rcases while_typing_data hty with ⟨hΔ, hbodyTy⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, htailStep⟩
  have hreadyBody : StmtReadyConcrete Δ σ body :=
    while_ready_body_data hready
  have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
    hbodyNorm hreadyBody hbodyStep
  have hreadyTail : StmtReadyConcrete Δ σ1 (.whileStmt c body) :=
    while_ready_after_body_normal hbodyTy hσ1 hready hbodyStep
  exact htail hσ1 hreadyTail htailStep


theorem while_normal_body_continue_case_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .continueResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    (∃ σ1,
      BigStepStmt σ body .continueResult σ1 ∧
      BigStepStmt σ1 (.whileStmt c body) .normal σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hbodyCont htail hcase
  rcases while_typing_data hty with ⟨hΔ, hbodyTy⟩
  subst hΔ
  rcases hcase with ⟨σ1, hbodyStep, htailStep⟩
  have hreadyBody : StmtReadyConcrete Δ σ body :=
    while_ready_body_data hready
  have hσ1 : ScopedTypedStateConcrete Δ σ1 :=
    hbodyCont hreadyBody hbodyStep
  have hreadyTail : StmtReadyConcrete Δ σ1 (.whileStmt c body) :=
    while_ready_after_body_continue hbodyTy hσ1 hready hbodyStep
  exact htail hσ1 hreadyTail htailStep


theorem while_normal_preserves_scoped_typed_state_from_body_and_tail
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .normal σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    (∀ {σ1},
      StmtReadyConcrete Γ σ body →
      BigStepStmt σ body .continueResult σ1 →
      ScopedTypedStateConcrete Γ σ1) →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep hbodyNorm hbodyCont htail
  rcases while_normal_data hstep with hstop | hnorm | hcont
  · exact while_normal_stop_case_preserves_scoped_typed_state
      hty hσ hstop
  · exact while_normal_body_normal_case_preserves_scoped_typed_state
      hty hσ hready hbodyNorm htail hnorm
  · exact while_normal_body_continue_case_preserves_scoped_typed_state
      hty hσ hready hbodyCont htail hcont


/- =========================================================
   3. primitive body の corollary
   ========================================================= -/

theorem primitive_normal_stmt_no_continue
    {σ σ' : State} {st : CppStmt} :
    PrimitiveNormalStmt st →
    ¬ BigStepStmt σ st .continueResult σ' := by
  intro hprim hcont
  cases st <;>
    simp [PrimitiveNormalStmt] at hprim <;>
    cases hcont


theorem primitive_body_while_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    PrimitiveNormalStmt body →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    (∀ {σ1},
      ScopedTypedStateConcrete Γ σ1 →
      StmtReadyConcrete Γ σ1 (.whileStmt c body) →
      BigStepStmt σ1 (.whileStmt c body) .normal σ' →
      ScopedTypedStateConcrete Γ σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep htail
  rcases while_typing_data hty with ⟨hΔ, hbodyTy⟩
  refine while_normal_preserves_scoped_typed_state_from_body_and_tail
    hty hσ hready hstep ?_ ?_ ?_
  · intro σ1 hreadyBody hbodyStep
    exact primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprim hbodyTy hσ hreadyBody hbodyStep
  · intro σ1 hreadyBody hbodyStep
    exfalso
    exact primitive_normal_stmt_no_continue hprim hbodyStep
  · intro σ1 hσ1 hreadyTail htailStep
    exact htail hσ1 hreadyTail htailStep


theorem while_normal_preserves_scoped_typed_state_concrete_of_primitive_body
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt} :
    PrimitiveNormalStmt body →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.whileStmt c body) .normal σ' →
    WhileTailClosed Γ σ' c body →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprim hty hσ hready hstep htail
  exact primitive_body_while_normal_preserves_scoped_typed_state_concrete
    hprim hty hσ hready hstep htail

end Cpp
