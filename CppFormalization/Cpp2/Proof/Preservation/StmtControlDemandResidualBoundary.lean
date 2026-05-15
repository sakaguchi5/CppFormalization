import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandRecursorCore

namespace Cpp

/-!
# Proof.Preservation.StmtControlDemandResidualBoundary

Demand-side residual boundaries for sequencing, block tails, and while tails.

The old residual-boundary vocabulary packages `StmtReadyConcrete` /
`BlockReadyConcrete` at the residual program point.  That is intentionally a
whole-program readiness notion: for example, `ite` readiness contains both
branches and `seq` readiness contains a pre-state tail readiness witness.

`StmtExecutionDemand` / `BlockExecutionDemand` are different.  They are
path-sensitive and store the demand only for the execution path actually taken.
So an aligned demand should not be coerced back into ordinary readiness.
Instead, this file gives the demand-side residual boundary used by the
axiom-free demand recursor.
-/

/--
Demand-side residual boundary for the tail statement of a sequence after the
head statement has finished normally.

It records the residual environment, the tail demand at the actual post-state,
the concrete tail step, alignment between them, and the scoped/typed post-state
needed to consume the tail demand.
-/
def SeqDemandResidualBoundary
    (Δ : TypeEnv) (σ₁ : State) (t : CppStmt)
    (ctrl : CtrlResult) (σ₂ : State) : Prop :=
  ∃ Θ,
    ∃ demand : StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ,
      ∃ step : BigStepStmt σ₁ t ctrl σ₂,
        StmtDemandFollowsStep demand step ∧
        ScopedTypedStateConcrete Θ σ₁

/--
Demand-side residual boundary for the tail of a block after the head statement
has finished normally.
-/
def ConsDemandResidualBoundary
    (Δ : TypeEnv) (σ₁ : State) (ss : StmtBlock)
    (ctrl : CtrlResult) (σ₂ : State) : Prop :=
  ∃ Θ,
    ∃ demand : BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ,
      ∃ step : BigStepBlock σ₁ ss ctrl σ₂,
        BlockDemandFollowsStep demand step ∧
        ScopedTypedStateConcrete Θ σ₁

/--
Demand-side tail boundary for a `while` re-entry point after the body finishes
with `.normal` or `.continueResult`.
-/
def WhileTailDemandBoundary
    (Γ Δ : TypeEnv) (σ₁ : State) (c : ValExpr) (body : CppStmt)
    (ctrl : CtrlResult) (σ₂ : State) : Prop :=
  ∃ demand : StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ₂ Δ,
    ∃ step : BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂,
      StmtDemandFollowsStep demand step ∧
      ScopedTypedStateConcrete Γ σ₁

/-- Consume a sequence demand-side residual boundary to preserve the tail. -/
theorem seq_demand_residual_boundary_preserves
    {Δ : TypeEnv} {σ₁ σ₂ : State} {t : CppStmt} {ctrl : CtrlResult}
    (B : SeqDemandResidualBoundary Δ σ₁ t ctrl σ₂) :
    ScopedTypedStateConcrete Δ σ₂ := by
  rcases B with ⟨Θ, demand, step, hfollows, hσ₁⟩
  exact stmt_preservation_from_demand_follows hfollows hσ₁

/-- Consume a block-tail demand-side residual boundary to preserve the tail. -/
theorem cons_demand_residual_boundary_preserves
    {Δ : TypeEnv} {σ₁ σ₂ : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (B : ConsDemandResidualBoundary Δ σ₁ ss ctrl σ₂) :
    ScopedTypedStateConcrete Δ σ₂ := by
  rcases B with ⟨Θ, demand, step, hfollows, hσ₁⟩
  exact block_preservation_from_demand_follows hfollows hσ₁

/-- Consume a while-tail demand boundary to preserve the tail loop. -/
theorem while_tail_demand_boundary_preserves
    {Γ Δ : TypeEnv} {σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {ctrl : CtrlResult}
    (B : WhileTailDemandBoundary Γ Δ σ₁ c body ctrl σ₂) :
    ScopedTypedStateConcrete Δ σ₂ := by
  rcases B with ⟨demand, step, hfollows, hσ₁⟩
  exact stmt_preservation_from_demand_follows hfollows hσ₁

/--
Build the tail demand boundary from the two aligned pieces of a `seqNormal`
execution.

This theorem intentionally takes the already-exposed head/tail alignment proofs
instead of eliminating a whole `StmtDemandFollowsStep` proof again.  This is the
same shape as the successful demand recursor: after matching on the alignment
evidence, the recursive branches should pass the constructor fields forward.
-/
theorem seq_demand_residual_boundary_of_seqNormal_follows
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s t : CppStmt} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepStmt σ₁ t ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : StmtDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    SeqDemandResidualBoundary Δ σ₁ t ctrl σ₂ := by
  exact ⟨Θ, dTail, stepTail, hfTail,
    stmt_preservation_from_demand_follows hfHead hσ⟩

/--
Build the block-tail demand boundary from the two aligned pieces of a block
`consNormal` execution.
-/
theorem cons_demand_residual_boundary_of_consNormal_follows
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepBlock σ₁ ss ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : BlockDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ConsDemandResidualBoundary Δ σ₁ ss ctrl σ₂ := by
  exact ⟨Θ, dTail, stepTail, hfTail,
    stmt_preservation_from_demand_follows hfHead hσ⟩

/--
Build the re-entry demand boundary from the aligned body/tail pieces of a
`whileTrueNormal` execution.
-/
theorem while_tail_demand_boundary_of_true_normal_follows
    {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {c : ValExpr} {body : CppStmt} {ctrl : CtrlResult}
    {dBody : StmtExecutionDemand Γ σ body .normal σ₁ Γ}
    {dTail : StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ₂ Δ}
    {stepBody : BigStepStmt σ body .normal σ₁}
    {stepTail : BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂}
    (hfBody : StmtDemandFollowsStep dBody stepBody)
    (hfTail : StmtDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    WhileTailDemandBoundary Γ Δ σ₁ c body ctrl σ₂ := by
  exact ⟨dTail, stepTail, hfTail,
    stmt_preservation_from_demand_follows hfBody hσ⟩

/--
Build the re-entry demand boundary from the aligned body/tail pieces of a
`whileTrueContinue` execution.
-/
theorem while_tail_demand_boundary_of_true_continue_follows
    {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {c : ValExpr} {body : CppStmt} {ctrl : CtrlResult}
    {dBody : StmtExecutionDemand Γ σ body .continueResult σ₁ Γ}
    {dTail : StmtExecutionDemand Γ σ₁ (.whileStmt c body) ctrl σ₂ Δ}
    {stepBody : BigStepStmt σ body .continueResult σ₁}
    {stepTail : BigStepStmt σ₁ (.whileStmt c body) ctrl σ₂}
    (hfBody : StmtDemandFollowsStep dBody stepBody)
    (hfTail : StmtDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    WhileTailDemandBoundary Γ Δ σ₁ c body ctrl σ₂ := by
  exact ⟨dTail, stepTail, hfTail,
    stmt_preservation_from_demand_follows hfBody hσ⟩

end Cpp
