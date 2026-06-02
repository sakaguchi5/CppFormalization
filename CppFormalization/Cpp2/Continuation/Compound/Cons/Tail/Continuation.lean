import CppFormalization.Cpp2.Continuation.Compound.Cons.Tail.Components

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail continuation

The continuation target of a cons-normal route is the block tail in the current
already-open block environment.

This file is intentionally indexed by `HeadNormalRouteCore`: continuation is a
post-route dynamic fact, not a wrapper around the legacy tail adequacy payload.
-/


structure PostState
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  postState : PostStateAt Γ σ1

/--
Replay invariant for the selected cons tail route.

The invariant is now componentized: it no longer stores a bare `BlockReplayAt`.
The materialized replay is obtained from the block-tail runtime replay
components.
-/
structure ReplayInvariant
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  components : RuntimeReplayComponentsAtRouteCI route

structure ContinuationInput
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  postState : PostState route
  replay : ReplayInvariant route

namespace ReplayInvariant

def blockReplay
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : ReplayInvariant route) :
    BlockReplayAt Γ σ1 tail :=
  h.components.toBlockReplay

def ready
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : ReplayInvariant route) :
    BlockReadyConcrete Γ σ1 tail :=
  h.components.ready

/-- Compatibility constructor for callers that already carry a block replay witness. -/
def ofBlockReplay
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : BlockReplayAt Γ σ1 tail) :
    ReplayInvariant route :=
  { components := RuntimeReplayComponentsAtRouteCI.ofBlockReplay h }

end ReplayInvariant

namespace ContinuationInput

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : ContinuationInput route) :
    BlockContinuationDynamicBoundary Γ σ1 tail :=
  { state := h.postState.postState.state
    safe := h.replay.ready }

/-- Compatibility helper for callers still carrying the legacy full route. -/
def ofLegacy
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (h : ContinuationInput route.toCore) :
    ContinuationInput route.toCore :=
  h

end ContinuationInput

end Tail
end Cons
end CompoundContinuation
end Cpp
