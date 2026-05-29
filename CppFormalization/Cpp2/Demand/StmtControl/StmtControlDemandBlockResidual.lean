import CppFormalization.Cpp2.Demand.StmtControl.StmtControlDemandResidualBoundary

namespace Cpp

/-!
# Proof.Preservation.StmtControlDemandBlockResidual

Demand-facing block-tail residual route.

This is the parallel demand-side replacement target for the ordinary-readiness
route in `Closure.Internal.BlockBodyNormalPreservation`.

It does **not** prove `cons_block_ready_tail_after_head_normal`: that theorem
asks for ordinary `BlockReadyConcrete` at the post-state and remains exact-tail
debt.  Instead, this file keeps the aligned block-tail demand as the residual
execution boundary.
-/

/--
Demand-side residual-boundary reconstruction for a block `consNormal` execution.

This is the demand analogue of `cons_head_normal_preserves_residual_boundary`,
but it produces `ConsDemandResidualBoundary` instead of ordinary
`ConsResidualBoundary`.
-/
theorem cons_normal_preserves_demand_residual_boundary
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepBlock σ₁ ss ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : BlockDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ConsDemandResidualBoundary Δ σ₁ ss ctrl σ₂ :=
  cons_demand_residual_boundary_of_consNormal_follows hfHead hfTail hσ

/--
Full demand-side preservation for a block `consNormal` execution, factored
through the block-tail demand residual boundary.

This is the replacement shape for callers that do not actually need ordinary
post-state `BlockReadyConcrete` for the tail.
-/
theorem cons_normal_preserves_scoped_typed_state_from_demand_residual_boundary
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepBlock σ₁ ss ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : BlockDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ₂ := by
  have B : ConsDemandResidualBoundary Δ σ₁ ss ctrl σ₂ :=
    cons_normal_preserves_demand_residual_boundary hfHead hfTail hσ
  exact cons_demand_residual_boundary_preserves B

end Cpp
