import CppFormalization.Cpp2.Proof.Preservation.Demand.Block

namespace Cpp

/-!
# Proof.Preservation.Demand.Inversions

Constructor inversions for execution demand.

These replace the old readiness-transport projections.  For `seq` and block
`cons`, the useful fact is not that tail readiness was transported.  The useful
fact is that the demand evidence already contains the tail demand at the
post-state where execution actually reaches the tail.
-/

theorem seq_demand_cases
    {Γ Δ : TypeEnv} {σ σ₂ : State} {s t : CppStmt} {ctrl : CtrlResult} :
    StmtExecutionDemand Γ σ (.seq s t) ctrl σ₂ Δ →
      (∃ σ₁ Θ,
        StmtExecutionDemand Γ σ s .normal σ₁ Θ ∧
        StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ) ∨
      StmtExecutionDemand Γ σ s ctrl σ₂ Δ := by
  intro h
  cases h with
  | seqNormal hHead hTail =>
      exact Or.inl ⟨_, _, hHead, hTail⟩
  | seqBreak hHead =>
      exact Or.inr hHead
  | seqContinue hHead =>
      exact Or.inr hHead
  | seqReturn hHead =>
      exact Or.inr hHead

theorem cons_demand_cases
    {Γ Δ : TypeEnv} {σ σ₂ : State} {s : CppStmt} {ss : StmtBlock}
    {ctrl : CtrlResult} :
    BlockExecutionDemand Γ σ (.cons s ss) ctrl σ₂ Δ →
      (∃ σ₁ Θ,
        StmtExecutionDemand Γ σ s .normal σ₁ Θ ∧
        BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ) ∨
      StmtExecutionDemand Γ σ s ctrl σ₂ Δ := by
  intro h
  cases h with
  | consNormal hHead hTail =>
      exact Or.inl ⟨_, _, hHead, hTail⟩
  | consBreak hHead =>
      exact Or.inr hHead
  | consContinue hHead =>
      exact Or.inr hHead
  | consReturn hHead =>
      exact Or.inr hHead

theorem ite_demand_cases
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt}
    {ctrl : CtrlResult} :
    StmtExecutionDemand Γ σ (.ite c s t) ctrl σ' Δ →
      (HasValueType Γ c (.base .bool) ∧
        ExprExecutionDemand Γ σ c (.base .bool) ∧
        BigStepValue σ c (.bool true) ∧
        StmtExecutionDemand Γ σ s ctrl σ' Δ) ∨
      (HasValueType Γ c (.base .bool) ∧
        ExprExecutionDemand Γ σ c (.base .bool) ∧
        BigStepValue σ c (.bool false) ∧
        StmtExecutionDemand Γ σ t ctrl σ' Δ) := by
  intro h
  cases h with
  | iteTrue hc hready hcond hbranch =>
      exact Or.inl ⟨hc, hready, hcond, hbranch⟩
  | iteFalse hc hready hcond hbranch =>
      exact Or.inr ⟨hc, hready, hcond, hbranch⟩

theorem block_stmt_demand_inv
    {Γ Δ : TypeEnv} {σ σ₂ : State} {ss : StmtBlock} {ctrl : CtrlResult} :
    StmtExecutionDemand Γ σ (.block ss) ctrl σ₂ Δ →
    ∃ Θ σ₀ σ₁,
      OpenScope σ σ₀ ∧
      TopFrameExtensionOf Γ Θ ∧
      BlockExecutionDemand (pushTypeScope Γ) σ₀ ss ctrl σ₁ Θ ∧
      CloseScope σ₁ σ₂ ∧
      Δ = Γ := by
  intro h
  cases h with
  | block hopen hExt hbody hclose =>
      exact ⟨_, _, _, hopen, hExt, hbody, hclose, rfl⟩

end Cpp
