import CppFormalization.Cpp2.Continuation.Compound.Cons.Route

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons block-tail replay components

This file is the block-tail analogue of the seq tail component split.

The components are indexed by the selected cons head-normal route.  They are not
general readiness transport principles: they describe why the remaining block
tail can be replayed at the post-state of this particular head-normal route.

The current materialization point is still `BlockReplayAt Γ σ1 tail`.  The four
component fields below make the future C++-meaningful split explicit:
block constructor shape, ordinary reads, dereference stability, and load
readability.
-/


/--
Block-constructor replay for the selected cons tail route.

This records the constructor-level replay witness for the remaining block tail at
the route's post-environment and post-state.  Later refinements can split this by
`BlockReplayAt` constructor without changing the continuation surface.
-/
structure BlockConstructorReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  replay : BlockReplayAt Γ σ1 tail

/--
Ordinary-read replay for the selected cons tail route.

This is the hook for the non-clobbering part of block-tail replay: the head
normal step must not invalidate the ordinary values/places that the tail block
replays.
-/
structure OrdinaryReadReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  replay : BlockReplayAt Γ σ1 tail

/--
Pointer/dereference stability for the selected cons tail route.

This is the route-local place where C++ alias/lifetime obligations for tail block
dereferences belong.  It deliberately does not import or reuse any legacy
readiness-transport package.
-/
structure PointerDerefStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  replay : BlockReplayAt Γ σ1 tail

/--
Load-readability preservation for the selected cons tail route.

This is the route-local hook for preserving readable/live/initialized loads used
by the remaining block tail after the head statement has completed normally.
-/
structure LoadReadabilityPreservationAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  replay : BlockReplayAt Γ σ1 tail

/--
Runtime replay components for the selected cons tail route.

The four fields are the block-tail split points corresponding to the seq-tail
component package.  The continuation layer consumes this package by
materializing an ordinary `BlockReplayAt`, then obtains readiness from the replay
core.
-/
structure RuntimeReplayComponentsAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Prop where
  blockShape : BlockConstructorReplayAtRouteCI route
  ordinaryReads : OrdinaryReadReplayAtRouteCI route
  derefPointer : PointerDerefStabilityAtRouteCI route
  loadReadability : LoadReadabilityPreservationAtRouteCI route

namespace RuntimeReplayComponentsAtRouteCI

/-- Materialize the route-local components as the replay witness consumed by continuation. -/
def toBlockReplay
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : RuntimeReplayComponentsAtRouteCI route) :
    BlockReplayAt Γ σ1 tail :=
  h.blockShape.replay

/-- Block-tail readiness follows from the materialized replay core. -/
def ready
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : RuntimeReplayComponentsAtRouteCI route) :
    BlockReadyConcrete Γ σ1 tail :=
  h.toBlockReplay.ready

/--
Compatibility constructor from an already-materialized block replay witness.

This is not a trivial inhabitant: callers still have to provide the actual
post-route `BlockReplayAt`.  It only populates the named split fields with the
same current witness until the components are refined independently.
-/
def ofBlockReplay
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : BlockReplayAt Γ σ1 tail) :
    RuntimeReplayComponentsAtRouteCI route :=
  { blockShape := { replay := h }
    ordinaryReads := { replay := h }
    derefPointer := { replay := h }
    loadReadability := { replay := h } }

end RuntimeReplayComponentsAtRouteCI

end Tail
end Cons
end CompoundContinuation
end Cpp
