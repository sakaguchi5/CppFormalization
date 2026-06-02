import CppFormalization.Cpp2.Continuation.Compound.Seq.Route

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail replay components

This file absorbs the valuable route-local replay vocabulary that used to live in
the old seq-tail replay obligation family, without importing that legacy family.

The components are intentionally indexed by the selected core route.  They are
not general readiness transport principles: they describe why the tail statement
can be replayed at the post-environment and post-state of this particular normal
seq route.

The current materialization point is still `StmtReplayAt route.Θ σ1 t`.  The
four component fields below make the future C++-meaningful split explicit:
constructor shape, ordinary reads, dereference stability, and load readability.
-/


/--
Statement-constructor replay for the selected seq tail route.

This records the constructor-level replay witness for `t` at the route's
post-environment and post-state.  Later refinements can split this by
`StmtReplayAt` constructor without changing the continuation surface.
-/
structure StmtConstructorReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  replay : StmtReplayAt route.Θ σ1 t

/--
Ordinary-read replay for the selected seq tail route.

This is the hook for the non-clobbering part of tail replay: the left normal
step must not invalidate the ordinary values/places that the tail replays.
At this stage it shares the same materialized replay witness, but it is named
separately so later proofs can replace it by a narrower read-footprint theorem.
-/
structure OrdinaryReadReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  replay : StmtReplayAt route.Θ σ1 t

/--
Pointer/dereference stability for the selected seq tail route.

This is the route-local place where C++ alias/lifetime obligations for tail
dereferences belong.  It deliberately does not import or reuse the legacy
seq-tail replay package.
-/
structure PointerDerefStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  replay : StmtReplayAt route.Θ σ1 t

/--
Load-readability preservation for the selected seq tail route.

This is the route-local hook for preserving readable/live/initialized loads
used by the tail after the left side has completed normally.
-/
structure LoadReadabilityPreservationAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  replay : StmtReplayAt route.Θ σ1 t

/--
Runtime replay components for the selected seq tail route.

The four fields are the valuable split points formerly hidden behind the old
seq-tail replay surface.  The continuation layer consumes this package by
materializing an ordinary `StmtReplayAt`, then obtains readiness from the replay
core.
-/
structure RuntimeReplayComponentsAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  stmtShape : StmtConstructorReplayAtRouteCI route
  ordinaryReads : OrdinaryReadReplayAtRouteCI route
  derefPointer : PointerDerefStabilityAtRouteCI route
  loadReadability : LoadReadabilityPreservationAtRouteCI route

namespace RuntimeReplayComponentsAtRouteCI

/-- Materialize the route-local components as the replay witness consumed by continuation. -/
def toStmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : RuntimeReplayComponentsAtRouteCI route) :
    StmtReplayAt route.Θ σ1 t :=
  h.stmtShape.replay

/-- Tail readiness follows from the materialized replay core. -/
def ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : RuntimeReplayComponentsAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t :=
  h.toStmtReplay.ready

/--
Compatibility constructor from an already-materialized replay witness.

This is not a trivial inhabitant: callers still have to provide the actual
post-route `StmtReplayAt`.  It only populates the named split fields with the
same current witness until the components are refined independently.
-/
def ofStmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : StmtReplayAt route.Θ σ1 t) :
    RuntimeReplayComponentsAtRouteCI route :=
  { stmtShape := { replay := h }
    ordinaryReads := { replay := h }
    derefPointer := { replay := h }
    loadReadability := { replay := h } }

end RuntimeReplayComponentsAtRouteCI

end Tail
end Seq
end CompoundContinuation
end Cpp
