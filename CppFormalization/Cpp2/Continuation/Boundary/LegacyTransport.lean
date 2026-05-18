import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Contracts.Obligations.ReadinessTransportNormalCore

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.LegacyTransport

Compatibility constructors from the legacy unrestricted readiness transport
obligation to continuation dynamic boundaries.

This module is intentionally transitional.  It keeps the existing proof kernel
building while changing the public shape from

`pre readiness -> post readiness`

to

`post-state continuation dynamic boundary`.

The final route should replace these constructors by route-specific
continuation constructors using preservation plus stability/replay obligations.
-/

theorem stmt_continuation_dynamic_of_legacy_transport
    {Γ Δ Ω : TypeEnv} {σ σ' : State} {head t : CppStmt}
    {k : ControlKind}
    (hctx : NormalTransportCtx Γ Δ σ σ' head)
    (htyTail : HasTypeStmtCI k Δ t Ω)
    (hreadyTailPre : StmtReadyConcrete Γ σ t) :
    StmtContinuationDynamicBoundary Δ σ' t := by
  exact
    { state := hctx.hpost
      safe := stmt_ready_transport_of_normal hctx htyTail hreadyTailPre }

theorem block_continuation_dynamic_of_legacy_transport
    {Γ Δ Ω : TypeEnv} {σ σ' : State} {head : CppStmt}
    {ss : StmtBlock} {k : ControlKind}
    (hctx : NormalTransportCtx Γ Δ σ σ' head)
    (htyTail : HasTypeBlockCI k Δ ss Ω)
    (hreadyTailPre : BlockReadyConcrete Γ σ ss) :
    BlockContinuationDynamicBoundary Δ σ' ss := by
  exact
    { state := hctx.hpost
      safe := block_ready_transport_of_normal hctx htyTail hreadyTailPre }

end Cpp
