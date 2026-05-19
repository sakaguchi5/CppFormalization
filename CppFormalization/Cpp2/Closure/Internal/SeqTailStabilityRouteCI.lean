import CppFormalization.Cpp2.Closure.Internal.SeqScaffoldRouteCI
import CppFormalization.Cpp2.Continuation.Boundary.Body

namespace Cpp

/-!
# Seq tail stability and continuation boundary

Extracted from `FunctionBodyCaseSplitCI.lean`.
This file owns route-local tail replay/stability and continuation assembly.
-/

/- =========================================================
   Seq tail route-stability / continuation decomposition
   ========================================================= -/

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


/--
Current post-state component obligation.

This is still an axiom for progress, but it is no longer mixed with tail runtime
readiness.  It should eventually be replaced by ordinary normal preservation.
-/
axiom seq_tail_post_state_at_route_ci_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailPostStateAtRouteCI route

/--
Current read-set non-clobbering obligation for the selected route.

Still a placeholder, but now individually named.
-/
axiom seq_tail_read_set_non_clobber_at_route_ci_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailReadSetNonClobberAtRouteCI route

/--
Current pointer/deref stability obligation for the selected route.

Still a placeholder, but now individually named.
-/
axiom seq_tail_pointer_deref_stability_at_route_ci_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailPointerDerefStabilityAtRouteCI route

/--
Current load-readability preservation obligation for the selected route.

Still a placeholder, but now individually named.
-/
axiom seq_tail_load_readability_preservation_at_route_ci_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailLoadReadabilityPreservationAtRouteCI route

/--
Current runtime replay components for the selected route, assembled from the
three named C++-meaningful obligations.
-/
def seq_tail_runtime_replay_components_at_route_ci_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailRuntimeReplayComponentsAtRouteCI route :=
  { readSet :=
      seq_tail_read_set_non_clobber_at_route_ci_of_entry hentry route
    derefPointer :=
      seq_tail_pointer_deref_stability_at_route_ci_of_entry hentry route
    loadReadability :=
      seq_tail_load_readability_preservation_at_route_ci_of_entry hentry route }

/--
Current runtime replay component obligation.

Compatibility name.  The direct coarse axiom has been replaced by named
component obligations plus a materialization obligation.
-/
def seq_tail_runtime_replay_at_route_ci_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailRuntimeReplayAtRouteCI route :=
  seq_tail_runtime_replay_at_route_ci_of_components
    hentry
    route
    (seq_tail_runtime_replay_components_at_route_ci_of_entry hentry route)

/--
Current coarse route-local tail stability obligation.

Compatibility name assembled from the newly split obligations.
-/
def seq_tail_stability_at_route_ci_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailStabilityAtRouteCI route :=
  seq_tail_stability_at_route_ci_of_parts
    route
    (seq_tail_post_state_at_route_ci_of_entry hentry route)
    (seq_tail_runtime_replay_at_route_ci_of_entry hentry route)

/--
Legacy compatibility constructor for the post-state component from the old
exact-tail route.
-/
noncomputable def seq_tail_post_state_at_route_ci_of_exact_tail
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailPostStateAtRouteCI route := by
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      mkWhileReentry route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
  exact { postState := hσ1 }

/--
Legacy compatibility constructor for the runtime replay component from the old
exact-tail route.
-/
noncomputable def seq_tail_runtime_replay_at_route_ci_of_exact_tail
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailRuntimeReplayAtRouteCI route := by
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      mkWhileReentry route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
  have hreadyRight : StmtReadyConcrete route.Θ σ1 t :=
    seq_ready_right_after_left_normal route.hleft hσ1 hentry.dynamic.safe route.hstepLeft
  exact SeqTailRuntimeReplayAtRouteCI.ofTailReady hreadyRight

/--
Legacy compatibility constructor from the old exact-tail route.

This keeps the old proof path available, but it now also passes through the
post-state/runtime split.
-/
noncomputable def seq_tail_stability_at_route_ci_of_exact_tail
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailStabilityAtRouteCI route :=
  seq_tail_stability_at_route_ci_of_parts
    route
    (seq_tail_post_state_at_route_ci_of_exact_tail mkWhileReentry hentry route)
    (seq_tail_runtime_replay_at_route_ci_of_exact_tail mkWhileReentry hentry route)

/--
Build the full post-state tail continuation from the selected route plus the
route-local stability contract.

This is the central decomposition theorem/definition: static and adequacy come
from the selected route, while dynamic readiness comes from the explicit
stability contract.
-/
noncomputable def seq_tail_continuation_boundary_ci_of_head_normal_route
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (stability : SeqTailStabilityAtRouteCI route) :
    StmtContinuationBoundaryCI route.Θ σ1 t :=
  { structural := seq_tail_structural_boundary_of_entry hentry
    static := route.tail.static
    dynamic := stability.toStmtContinuationDynamicBoundary
    adequacy := route.tail.support.toBodyAdequacyCI }

/--
Theorem-backed post-state component, assuming the existing normal-preservation
provider needed by the current repository.

This is the important conceptual cut: post-state preservation is not a C++
tail-stability contract.  It is a preservation theorem once the normal route is
known.
-/
noncomputable def seq_tail_post_state_at_route_ci_of_preservation
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailPostStateAtRouteCI route := by
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      mkWhileReentry route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
  exact { postState := hσ1 }

/--
Assemble full route-local tail stability from theorem-backed post-state
preservation plus explicit runtime replay.

This is the preferred bridge when a caller can supply only the genuine runtime
contract.
-/
def seq_tail_stability_at_route_ci_of_preservation_and_runtime_replay
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (runtime : SeqTailRuntimeReplayAtRouteCI route) :
    SeqTailStabilityAtRouteCI route :=
  seq_tail_stability_at_route_ci_of_parts
    route
    (seq_tail_post_state_at_route_ci_of_preservation
      mkWhileReentry hentry route)
    runtime

/--
Assemble full route-local tail stability directly from named runtime replay
components.
-/
def seq_tail_stability_at_route_ci_of_preservation_and_runtime_components
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    SeqTailStabilityAtRouteCI route :=
  seq_tail_stability_at_route_ci_of_preservation_and_runtime_replay
    mkWhileReentry hentry route
    (seq_tail_runtime_replay_at_route_ci_of_components
      hentry route components)

/--
Build the full tail continuation from theorem-backed post-state preservation and
explicit runtime replay.
-/
noncomputable def seq_tail_continuation_boundary_ci_of_head_normal_route_from_runtime_replay
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (runtime : SeqTailRuntimeReplayAtRouteCI route) :
    StmtContinuationBoundaryCI route.Θ σ1 t :=
  seq_tail_continuation_boundary_ci_of_head_normal_route
    hentry
    route
    (seq_tail_stability_at_route_ci_of_preservation_and_runtime_replay
      mkWhileReentry hentry route runtime)

/--
Build the full tail continuation from theorem-backed post-state preservation and
named runtime replay components.
-/
noncomputable def seq_tail_continuation_boundary_ci_of_head_normal_route_from_runtime_components
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    StmtContinuationBoundaryCI route.Θ σ1 t :=
  seq_tail_continuation_boundary_ci_of_head_normal_route_from_runtime_replay
    mkWhileReentry
    hentry
    route
    (seq_tail_runtime_replay_at_route_ci_of_components
      hentry route components)


/--
Compatibility view of the route-local continuation boundary as an ordinary tail
closure boundary.
-/
noncomputable def seq_tail_closure_boundary_ci_of_head_normal_route_from_stability
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (stability : SeqTailStabilityAtRouteCI route) :
    BodyClosureBoundaryCI route.Θ σ1 t :=
  (seq_tail_continuation_boundary_ci_of_head_normal_route
    hentry route stability).toBodyClosureBoundaryCI

end Cpp
