import CppFormalization.Cpp2.Closure.Internal.SeqScaffoldRouteCI
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay
import CppFormalization.Cpp2.Continuation.Boundary.Seq

namespace Cpp

/-!
# Seq tail stability and continuation boundary

Extracted from `FunctionBodyCaseSplitCI.lean`.
This file owns route-local tail replay/stability and continuation assembly.
-/

/- =========================================================
   Seq tail route-stability / continuation decomposition
   ========================================================= -/


/-!
Seq tail replay/stability contract records were extracted to
`CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay`.
-/

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
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailPostStateAtRouteCI route := by
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
  exact { postState := hσ1 }

/--
Legacy compatibility constructor for the runtime replay component from the old
exact-tail route.
-/
noncomputable def seq_tail_runtime_replay_at_route_ci_of_exact_tail
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailRuntimeReplayAtRouteCI route := by
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
  have hreadyRight : StmtReadyConcrete route.Θ σ1 t :=
    seq_ready_right_after_left_normal route.hleft hσ1 hentry.dynamic.safe route.hstepLeft
  exact SeqTailRuntimeReplayAtRouteCI.ofTailReady hreadyRight

/--
Legacy compatibility constructor from the old exact-tail route.

This keeps the old proof path available, but it now also passes through the
post-state/runtime split.
-/
noncomputable def seq_tail_stability_at_route_ci_of_exact_tail
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailStabilityAtRouteCI route :=
  seq_tail_stability_at_route_ci_of_parts
    route
    (seq_tail_post_state_at_route_ci_of_exact_tail hentry route)
    (seq_tail_runtime_replay_at_route_ci_of_exact_tail hentry route)


/-!
Seq tail continuation-boundary assembly was extracted to
`CppFormalization.Cpp2.Continuation.Boundary.Seq`.
-/

/--
Theorem-backed post-state component, assuming the existing normal-preservation
provider needed by the current repository.

This is the important conceptual cut: post-state preservation is not a C++
tail-stability contract.  It is a preservation theorem once the normal route is
known.
-/
noncomputable def seq_tail_post_state_at_route_ci_of_preservation
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailPostStateAtRouteCI route := by
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
  exact { postState := hσ1 }

/--
Assemble full route-local tail stability from theorem-backed post-state
preservation plus explicit runtime replay.

This is the preferred bridge when a caller can supply only the genuine runtime
contract.
-/
def seq_tail_stability_at_route_ci_of_preservation_and_runtime_replay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (runtime : SeqTailRuntimeReplayAtRouteCI route) :
    SeqTailStabilityAtRouteCI route :=
  seq_tail_stability_at_route_ci_of_parts
    route
    (seq_tail_post_state_at_route_ci_of_preservation
      hentry route)
    runtime

/--
Assemble full route-local tail stability directly from named runtime replay
components.
-/
def seq_tail_stability_at_route_ci_of_preservation_and_runtime_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    SeqTailStabilityAtRouteCI route :=
  seq_tail_stability_at_route_ci_of_preservation_and_runtime_replay
    hentry route
    (seq_tail_runtime_replay_at_route_ci_of_components
      hentry route components)

/--
Build the full tail continuation from theorem-backed post-state preservation and
explicit runtime replay.
-/
noncomputable def seq_tail_continuation_boundary_ci_of_head_normal_route_from_runtime_replay
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
       hentry route runtime)

/--
Build the full tail continuation from theorem-backed post-state preservation and
named runtime replay components.
-/
noncomputable def seq_tail_continuation_boundary_ci_of_head_normal_route_from_runtime_components
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (components : SeqTailRuntimeReplayComponentsAtRouteCI route) :
    StmtContinuationBoundaryCI route.Θ σ1 t :=
  seq_tail_continuation_boundary_ci_of_head_normal_route_from_runtime_replay
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
