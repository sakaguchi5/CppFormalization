import CppFormalization.Cpp2.Demand.Preservation.Stmt

namespace Cpp

/-!
# Proof.Preservation.Demand.Block

Block-oriented aliases and small constructors for execution demand.

The mutually inductive statement/block demand definitions live in
`Demand.Stmt`; this file gives the block side a stable import surface.
-/

abbrev BlockDemand :=
  BlockExecutionDemand

abbrev StmtDemand :=
  StmtExecutionDemand

@[simp] theorem blockDemand_nil
    {Γ : TypeEnv} {σ : State} :
    BlockDemand Γ σ .nil .normal σ Γ :=
  BlockExecutionDemand.nil

theorem blockDemand_consNormal
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock} {ctrl : CtrlResult} :
    StmtExecutionDemand Γ σ s .normal σ₁ Θ →
    BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ →
    BlockDemand Γ σ (.cons s ss) ctrl σ₂ Δ :=
  BlockExecutionDemand.consNormal

end Cpp
