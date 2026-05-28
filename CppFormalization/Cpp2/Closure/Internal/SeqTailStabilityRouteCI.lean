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





end Cpp
