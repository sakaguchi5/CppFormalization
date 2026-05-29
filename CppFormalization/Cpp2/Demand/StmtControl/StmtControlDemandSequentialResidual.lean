import CppFormalization.Cpp2.Demand.StmtControl.StmtControlDemandResidualBoundary

namespace Cpp

/-!
# Proof.Preservation.StmtControlDemandSequentialResidual

Demand-facing sequence residual route.

This is the parallel demand-side replacement target for the ordinary-readiness
route in `Closure.Internal.SequentialNormalPreservation`.

It does **not** prove `seq_ready_right_after_left_normal`: that theorem asks for
ordinary `StmtReadyConcrete` at the post-state and remains exact-tail debt.
Instead, this file records the route that the demand preservation recursor uses:

* preserve the head normal execution;
* keep the already-aligned tail demand at the concrete post-state;
* consume that demand to preserve the tail execution.
-/

/--
Demand-side residual-boundary reconstruction for a `seqNormal` execution.

This is the demand analogue of the residual-boundary reconstruction performed by
`SequentialNormalPreservation`, but it produces `SeqDemandResidualBoundary`
instead of ordinary `SeqResidualBoundary`.
-/
theorem seq_normal_preserves_demand_residual_boundary
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s t : CppStmt} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepStmt σ₁ t ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : StmtDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    SeqDemandResidualBoundary Δ σ₁ t ctrl σ₂ :=
  seq_demand_residual_boundary_of_seqNormal_follows hfHead hfTail hσ

/--
Full demand-side preservation for a `seqNormal` execution, factored through the
sequence demand residual boundary.

This is the replacement shape for callers that do not actually need ordinary
post-state `StmtReadyConcrete` for the tail.
-/
theorem seq_normal_preserves_scoped_typed_state_from_demand_residual_boundary
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s t : CppStmt} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepStmt σ₁ t ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : StmtDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ₂ := by
  have B : SeqDemandResidualBoundary Δ σ₁ t ctrl σ₂ :=
    seq_normal_preserves_demand_residual_boundary hfHead hfTail hσ
  exact seq_demand_residual_boundary_preserves B

end Cpp
