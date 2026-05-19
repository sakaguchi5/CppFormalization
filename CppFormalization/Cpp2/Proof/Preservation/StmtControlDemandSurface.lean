import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandRecursorCore
import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandSequentialResidual
import CppFormalization.Cpp2.Proof.Preservation.StmtControlDemandBlockResidual

namespace Cpp

/-!
# Proof.Preservation.StmtControlDemandSurface

Public exact-tail-free surface for the demand preservation route.

The theorem names here are thin aliases.  Their purpose is to give callers a
single migration target when they do not need ordinary post-state
`StmtReadyConcrete` / `BlockReadyConcrete`, but only preservation along an
aligned execution demand.
-/

/-- Statement preservation from compatibility, demand, and step alignment. -/
theorem demand_surface_stmt_control_preserves
    {k : ControlKind} {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeStmtCI k Γ st Δ}
    {hstep : BigStepStmt σ st ctrl σ'}
    (hcomp : StmtControlCompatible hty hstep)
    (demand : StmtExecutionDemand Γ σ st ctrl σ' Δ)
    (hfollows : StmtDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  stmt_control_preserves_from_demand_follows hcomp demand hfollows

/-- Block preservation from compatibility, demand, and step alignment. -/
theorem demand_surface_block_control_preserves
    {k : ControlKind} {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {hty : HasTypeBlockCI k Γ ss Δ}
    {hstep : BigStepBlock σ ss ctrl σ'}
    (hcomp : BlockControlCompatible hty hstep)
    (demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ)
    (hfollows : BlockDemandFollowsStep demand hstep) :
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  block_control_preserves_from_demand_follows hcomp demand hfollows

/-- Demand-side sequence residual boundary for a `seqNormal` execution. -/
theorem demand_surface_seq_normal_residual
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
  seq_normal_preserves_demand_residual_boundary hfHead hfTail hσ

/-- Demand-side preservation for a `seqNormal` execution via its residual boundary. -/
theorem demand_surface_seq_normal_preserves
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s t : CppStmt} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : StmtExecutionDemand Θ σ₁ t ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepStmt σ₁ t ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : StmtDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ₂ :=
  seq_normal_preserves_scoped_typed_state_from_demand_residual_boundary
    hfHead hfTail hσ

/-- Demand-side block-tail residual boundary for a `consNormal` execution. -/
theorem demand_surface_cons_normal_residual
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
  cons_normal_preserves_demand_residual_boundary hfHead hfTail hσ

/-- Demand-side preservation for a `consNormal` execution via its residual boundary. -/
theorem demand_surface_cons_normal_preserves
    {Γ Θ Δ : TypeEnv} {σ σ₁ σ₂ : State}
    {s : CppStmt} {ss : StmtBlock} {ctrl : CtrlResult}
    {dHead : StmtExecutionDemand Γ σ s .normal σ₁ Θ}
    {dTail : BlockExecutionDemand Θ σ₁ ss ctrl σ₂ Δ}
    {stepHead : BigStepStmt σ s .normal σ₁}
    {stepTail : BigStepBlock σ₁ ss ctrl σ₂}
    (hfHead : StmtDemandFollowsStep dHead stepHead)
    (hfTail : BlockDemandFollowsStep dTail stepTail)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ₂ :=
  cons_normal_preserves_scoped_typed_state_from_demand_residual_boundary
    hfHead hfTail hσ

end Cpp
