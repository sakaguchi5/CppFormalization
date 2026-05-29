import CppFormalization.Cpp2.Demand.Preservation.ExecutionTrace
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete

namespace Cpp

/-!
# Proof.Preservation.Demand.ResidualBoundary

Lower-level demand-side residual boundary vocabulary.

This file contains only the boundary definitions.  It deliberately does not
import `StmtControlDemandRecursorCore`, so higher recursor files may import this
file without creating an import cycle.

The old readiness residual boundaries package `StmtReadyConcrete` /
`BlockReadyConcrete`.  These definitions instead package path-sensitive
execution demand aligned with the concrete big-step derivation.
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

end Cpp
