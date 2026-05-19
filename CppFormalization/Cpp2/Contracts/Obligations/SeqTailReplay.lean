import CppFormalization.Cpp2.Continuation.Route.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Boundary.Body.BodyClosureBoundaryCI

namespace Cpp

/-!
# Seq tail replay / stability obligations

Extracted aggressively from `Closure.Internal.SeqTailStabilityRouteCI`.
This module contains route-local tail replay and stability contracts.  These are
not closure shells: they are the conditions saying why the selected route can
enter the tail in the post-state.

Several components are still coarse placeholders.  The point of this move is to
make them visible as contract obligations, not as hidden closure internals.
-/

/--
Post-state component of the tail stability contract.

This is preservation-shaped: after the selected left-normal route, the route's
post-environment `route.Θ` and actual post-state `σ1` still agree concretely.
Long term, this component should be theorem-backed by normal preservation rather
than treated as a program contract.
-/
structure SeqTailPostStateAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  postState : ScopedTypedStateConcrete route.Θ σ1

/--
Name/scope/static component of the tail stability contract.

This is intentionally separated from runtime readiness.  The selected route
already determines `route.Θ`, and the tail static package lives exactly at that
environment.  This records the future split point for name-resolution and scope
stability.
-/
structure SeqTailNameScopeStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  typed0 : WellTypedFrom route.Θ t

/-- Read-set non-clobbering component for the selected tail route.

This is a deliberately small placeholder component.  Later it should be refined
into an actual read-set/effect separation predicate. -/
structure SeqTailReadSetNonClobberAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  witness : True

/-- Pointer/deref stability component for the selected tail route.

Later this should say that pointer values used by tail dereferences remain
valid/live/typed after the left route. -/
structure SeqTailPointerDerefStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  witness : True

/-- Load readability preservation component for the selected tail route.

Later this should say that places loaded by the tail remain readable, not merely
live. -/
structure SeqTailLoadReadabilityPreservationAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  witness : True

/--
Runtime replay component of the tail stability contract.

The three named subcomponents are the C++-meaningful future split points.  At
this stage, `tailReady` is still the coarse runtime fact, but it is no longer
mixed with post-state preservation or tail static/profile adequacy.
-/
structure SeqTailRuntimeReplayAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  readSet : SeqTailReadSetNonClobberAtRouteCI route
  derefPointer : SeqTailPointerDerefStabilityAtRouteCI route
  loadReadability : SeqTailLoadReadabilityPreservationAtRouteCI route
  tailReady : StmtReadyConcrete route.Θ σ1 t

namespace SeqTailRuntimeReplayAtRouteCI

/-- Compatibility constructor from the still-coarse tail readiness fact. -/
def ofTailReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (hready : StmtReadyConcrete route.Θ σ1 t) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := { witness := trivial }
    derefPointer := { witness := trivial }
    loadReadability := { witness := trivial }
    tailReady := hready }

end SeqTailRuntimeReplayAtRouteCI

/--
Route-local stability contract for the tail of `s; t`.


/--
Runtime replay components for the selected tail route.

This is the next refinement below `SeqTailRuntimeReplayAtRouteCI`: the C++
meaningful parts are named separately, and the remaining coarse step is only the
materialization theorem/obligation that turns those components into ordinary
`StmtReadyConcrete`.
-/
-/
structure SeqTailRuntimeReplayComponentsAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Prop where
  readSet : SeqTailReadSetNonClobberAtRouteCI route
  derefPointer : SeqTailPointerDerefStabilityAtRouteCI route
  loadReadability : SeqTailLoadReadabilityPreservationAtRouteCI route

/--
Materialize tail readiness from the named runtime replay components.

This is intentionally still an obligation.  The progress is that the obligation
is no longer "transport readiness after normal"; it is now "these concrete
runtime replay components are sufficient for the selected route's tail
readiness".
-/
axiom seq_tail_ready_of_runtime_replay_components_at_route_ci
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t

/-- Assemble the runtime replay package from named replay components. -/
def seq_tail_runtime_replay_at_route_ci_of_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    SeqTailRuntimeReplayAtRouteCI route :=
  { readSet := components.readSet
    derefPointer := components.derefPointer
    loadReadability := components.loadReadability
    tailReady :=
      seq_tail_ready_of_runtime_replay_components_at_route_ci
        hentry route components }

/--
Compared with the previous coarse version, this now has three visible layers:

* `postStatePart`: preservation-shaped post-state/environment agreement;
* `nameScopePart`: static/name/scope side of the selected tail;
* `runtimePart`: runtime replay/readiness side, with future C++ split points.

The important change is that the public subject is still the selected route,
not a global exact-tail readiness transport theorem.
-/
structure SeqTailStabilityAtRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  postStatePart : SeqTailPostStateAtRouteCI route
  nameScopePart : SeqTailNameScopeStabilityAtRouteCI route
  runtimePart : SeqTailRuntimeReplayAtRouteCI route

namespace SeqTailNameScopeStabilityAtRouteCI

/-- The current selected route already carries the coarse tail typing witness. -/
def ofRoute
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailNameScopeStabilityAtRouteCI route :=
  { typed0 := route.tail.static.typed0 }

end SeqTailNameScopeStabilityAtRouteCI

namespace SeqTailStabilityAtRouteCI

/-- Post-state projection preserved for old callers. -/
def postState
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    ScopedTypedStateConcrete route.Θ σ1 :=
  h.postStatePart.postState

/-- Runtime tail-readiness projection preserved for old callers. -/
def tailReady
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    StmtReadyConcrete route.Θ σ1 t :=
  h.runtimePart.tailReady

/-- The dynamic continuation boundary induced by a route-local stability proof. -/
def toStmtContinuationDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  { state := h.postState
    safe := h.tailReady }

/-- Compatibility view as the old body dynamic boundary. -/
def toBodyDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : SeqTailStabilityAtRouteCI route) :
    BodyDynamicBoundary route.Θ σ1 t :=
  h.toStmtContinuationDynamicBoundary.toBodyDynamicBoundary

end SeqTailStabilityAtRouteCI

/--
Assemble the route-local stability contract from its preservation/static/runtime
parts.

This is the preferred constructor for the next stage: callers should eventually
supply post-state preservation and runtime replay separately.
-/
def seq_tail_stability_at_route_ci_of_parts
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (postState : SeqTailPostStateAtRouteCI route)
    (runtime : SeqTailRuntimeReplayAtRouteCI route) :
    SeqTailStabilityAtRouteCI route :=
  { postStatePart := postState
    nameScopePart := SeqTailNameScopeStabilityAtRouteCI.ofRoute route
    runtimePart := runtime }

end Cpp
