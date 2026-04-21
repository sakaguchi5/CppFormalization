import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI

namespace Cpp

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

end Cpp
