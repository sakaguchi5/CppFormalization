import CppFormalization.Cpp2.Demand.StmtControl.StmtControlDemandSurface

namespace Cpp

/-!
# Proof.Preservation.StmtControlDemandProvider

Provider-shaped interface for the exact-tail-free demand preservation route.

The older normal-preservation provider surfaces are readiness-based: they consume
`StmtReadyConcrete` / `BlockReadyConcrete` and therefore tend to return to the
ordinary-readiness residual route, where `ReadinessTransportNormalExactTail`
still lives.

This file gives the demand-facing replacement surface.  Its providers consume
path-sensitive execution demand aligned with the concrete big-step derivation.
They do not need post-state ordinary readiness for sequence/block tails.
-/

/-- Statement preservation provider for one aligned execution demand. -/
structure StmtControlDemandPreservationProviderCI : Type where
  preserve :
    ∀ {Γ Δ : TypeEnv} {st : CppStmt}
      {σ : State} {ctrl : CtrlResult} {σ' : State}
      {demand : StmtExecutionDemand Γ σ st ctrl σ' Δ}
      {hstep : BigStepStmt σ st ctrl σ'},
      StmtDemandFollowsStep demand hstep →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ'

/-- Block preservation provider for one aligned execution demand. -/
structure BlockControlDemandPreservationProviderCI : Type where
  preserve :
    ∀ {Γ Δ : TypeEnv} {ss : StmtBlock}
      {σ : State} {ctrl : CtrlResult} {σ' : State}
      {demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ}
      {hstep : BigStepBlock σ ss ctrl σ'},
      BlockDemandFollowsStep demand hstep →
      ScopedTypedStateConcrete Γ σ →
      ScopedTypedStateConcrete Δ σ'

/-- Bundle statement and block demand preservation providers together. -/
structure StmtBlockControlDemandPreservationProviderCI : Type where
  stmt : StmtControlDemandPreservationProviderCI
  block : BlockControlDemandPreservationProviderCI

namespace StmtControlDemandPreservationProviderCI

/-- The theorem-backed statement demand provider. -/
def theoremBacked : StmtControlDemandPreservationProviderCI where
  preserve := by
    intro Γ Δ st σ ctrl σ' demand hstep hfollows hσ
    exact stmt_preservation_from_demand_follows hfollows hσ

/-- Normal-only view of a statement demand provider.

This is the direct demand-facing replacement shape for ready-based normal
preservation providers when callers do not need ordinary post-state readiness.
-/
theorem normal
    (P : StmtControlDemandPreservationProviderCI)
    {Γ Δ : TypeEnv} {st : CppStmt}
    {σ σ' : State}
    {demand : StmtExecutionDemand Γ σ st .normal σ' Δ}
    {hstep : BigStepStmt σ st .normal σ'} :
    StmtDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  P.preserve

end StmtControlDemandPreservationProviderCI

namespace BlockControlDemandPreservationProviderCI

/-- The theorem-backed block demand provider. -/
def theoremBacked : BlockControlDemandPreservationProviderCI where
  preserve := by
    intro Γ Δ ss σ ctrl σ' demand hstep hfollows hσ
    exact block_preservation_from_demand_follows hfollows hσ

/-- Normal-only view of a block demand provider.

This is the direct demand-facing replacement shape for ready-based block normal
preservation providers when callers do not need ordinary post-state readiness.
-/
theorem normal
    (P : BlockControlDemandPreservationProviderCI)
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ σ' : State}
    {demand : BlockExecutionDemand Γ σ ss .normal σ' Δ}
    {hstep : BigStepBlock σ ss .normal σ'} :
    BlockDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  P.preserve

end BlockControlDemandPreservationProviderCI

namespace StmtBlockControlDemandPreservationProviderCI

/-- The theorem-backed bundled demand provider. -/
def theoremBacked : StmtBlockControlDemandPreservationProviderCI where
  stmt := StmtControlDemandPreservationProviderCI.theoremBacked
  block := BlockControlDemandPreservationProviderCI.theoremBacked

/-- Statement projection from the bundled provider. -/
theorem stmt_preserve
    (P : StmtBlockControlDemandPreservationProviderCI)
    {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : StmtExecutionDemand Γ σ st ctrl σ' Δ}
    {hstep : BigStepStmt σ st ctrl σ'} :
    StmtDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  P.stmt.preserve

/-- Block projection from the bundled provider. -/
theorem block_preserve
    (P : StmtBlockControlDemandPreservationProviderCI)
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ}
    {hstep : BigStepBlock σ ss ctrl σ'} :
    BlockDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  P.block.preserve

end StmtBlockControlDemandPreservationProviderCI

/-- Public theorem-backed statement demand provider. -/
def stmtControlDemandPreservationProviderCI :
    StmtControlDemandPreservationProviderCI :=
  StmtControlDemandPreservationProviderCI.theoremBacked

/-- Public theorem-backed block demand provider. -/
def blockControlDemandPreservationProviderCI :
    BlockControlDemandPreservationProviderCI :=
  BlockControlDemandPreservationProviderCI.theoremBacked

/-- Public theorem-backed bundled statement/block demand provider. -/
def stmtBlockControlDemandPreservationProviderCI :
    StmtBlockControlDemandPreservationProviderCI :=
  StmtBlockControlDemandPreservationProviderCI.theoremBacked

/- =========================================================
   Surface aliases through the provider
   ========================================================= -/

/-- Statement preservation through the public demand provider. -/
theorem stmt_control_preserves_from_demand_provider
    {Γ Δ : TypeEnv} {st : CppStmt}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : StmtExecutionDemand Γ σ st ctrl σ' Δ}
    {hstep : BigStepStmt σ st ctrl σ'} :
    StmtDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  stmtControlDemandPreservationProviderCI.preserve

/-- Block preservation through the public demand provider. -/
theorem block_control_preserves_from_demand_provider
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ : State} {ctrl : CtrlResult} {σ' : State}
    {demand : BlockExecutionDemand Γ σ ss ctrl σ' Δ}
    {hstep : BigStepBlock σ ss ctrl σ'} :
    BlockDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  blockControlDemandPreservationProviderCI.preserve

/-- Normal statement preservation through the public demand provider. -/
theorem stmt_normal_preserves_from_demand_provider
    {Γ Δ : TypeEnv} {st : CppStmt}
    {σ σ' : State}
    {demand : StmtExecutionDemand Γ σ st .normal σ' Δ}
    {hstep : BigStepStmt σ st .normal σ'} :
    StmtDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  stmt_control_preserves_from_demand_provider

/-- Normal block preservation through the public demand provider. -/
theorem block_normal_preserves_from_demand_provider
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    {σ σ' : State}
    {demand : BlockExecutionDemand Γ σ ss .normal σ' Δ}
    {hstep : BigStepBlock σ ss .normal σ'} :
    BlockDemandFollowsStep demand hstep →
    ScopedTypedStateConcrete Γ σ →
    ScopedTypedStateConcrete Δ σ' :=
  block_control_preserves_from_demand_provider

end Cpp
