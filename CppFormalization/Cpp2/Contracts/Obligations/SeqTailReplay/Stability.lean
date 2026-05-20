import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.BaseMaterialization
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay.Structured

namespace Cpp

/-!
# Seq tail replay: stability package and fallback obligation
-/

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
