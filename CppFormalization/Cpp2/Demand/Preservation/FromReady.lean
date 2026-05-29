import CppFormalization.Cpp2.Demand.Preservation.Inversions

namespace Cpp

/-!
# Proof.Preservation.Demand.FromReady

Small bridges from existing readiness evidence into execution demand.

This file is intentionally conservative.  It does not claim that a ready `seq`
entry state determines a ready tail after the head runs.  Only local/primitive
bridges are provided here.  Composite demands should be built from path-local
subdemands.
-/

theorem skip_demand_of_ready
    {Γ : TypeEnv} {σ : State} :
    StmtReadyConcrete Γ σ .skip →
    StmtExecutionDemand Γ σ .skip .normal σ Γ := by
  intro _
  exact StmtExecutionDemand.skip

theorem exprStmt_demand_of_ready
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {v : Value} :
    StmtReadyConcrete Γ σ (.exprStmt e) →
    BigStepValue σ e v →
    ∃ τ,
      HasValueType Γ e τ ∧
      ExprExecutionDemand Γ σ e τ ∧
      StmtExecutionDemand Γ σ (.exprStmt e) .normal σ Γ := by
  intro hready hval
  cases hready with
  | exprStmt hty hExprReady =>
      exact ⟨_, hty, hExprReady,
        StmtExecutionDemand.exprStmt hty hExprReady hval⟩

theorem assign_demand_of_ready
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {e : ValExpr}
    {v : Value} :
    StmtReadyConcrete Γ σ (.assign p e) →
    BigStepValue σ e v →
    Assigns σ p v σ' →
    ∃ τ,
      HasPlaceType Γ p τ ∧
      PlaceExecutionDemand Γ σ p τ ∧
      HasValueType Γ e τ ∧
      ExprExecutionDemand Γ σ e τ ∧
      StmtExecutionDemand Γ σ (.assign p e) .normal σ' Γ := by
  intro hready hval hassign
  cases hready with
  | assign hpty hpReady hvty heReady =>
      exact ⟨_, hpty, hpReady, hvty, heReady,
        StmtExecutionDemand.assign hpty hpReady hvty heReady hval hassign⟩

theorem returnSome_demand_of_ready
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {v : Value} :
    StmtReadyConcrete Γ σ (.returnStmt (some e)) →
    BigStepValue σ e v →
    ∃ τ,
      HasValueType Γ e τ ∧
      ExprExecutionDemand Γ σ e τ ∧
      StmtExecutionDemand Γ σ (.returnStmt (some e)) (.returnResult (some v)) σ Γ := by
  intro hready hval
  cases hready with
  | returnSome hty hExprReady =>
      exact ⟨_, hty, hExprReady,
        StmtExecutionDemand.returnSome hty hExprReady hval⟩

theorem nil_block_demand_of_ready
    {Γ : TypeEnv} {σ : State} :
    BlockReadyConcrete Γ σ .nil →
    BlockExecutionDemand Γ σ .nil .normal σ Γ := by
  intro _
  exact BlockExecutionDemand.nil

end Cpp
