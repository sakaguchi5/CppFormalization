import CppFormalization.Cpp2.Closure.Internal.SeqClosureRouteCI
import CppFormalization.Cpp2.Continuation.Boundary.Body

namespace Cpp

/-!
# Seq runtime replay route wrappers

-/

/--
Route-aware seq shell with theorem-backed post-state preservation and an
explicit runtime replay callback.

Compared with `...with_replay_parts`, callers no longer supply the post-state
component; it is derived from normal preservation.  What remains visible is the
genuine runtime replay contract for the tail.
-/
theorem seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_replay
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailRuntimeReplay :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailRuntimeReplayAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_stability
      hentry
      leftClosure
      (fun route =>
        seq_tail_stability_at_route_ci_of_preservation_and_runtime_replay
          hentry
          route
          (tailRuntimeReplay route))
      tailClosure

/--
Body-boundary compatibility wrapper for theorem-backed post-state preservation
and explicit runtime replay.
-/
theorem seq_function_body_closure_boundary_ci_honest_with_runtime_replay
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailRuntimeReplay :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailRuntimeReplayAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyClosureBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_replay
      hentry
      leftClosure
      tailRuntimeReplay
      (fun route htail =>
        tailClosure route htail.toBodyClosureBoundaryCI)

/--
Route-aware seq shell with theorem-backed post-state preservation and named
runtime replay components.
-/
theorem seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_components
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailRuntimeComponents :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailRuntimeReplayComponentsAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_replay
      hentry
      leftClosure
      (fun route =>
        seq_tail_runtime_replay_at_route_ci_of_components
          hentry route (tailRuntimeComponents route))
      tailClosure

/--
Route-aware seq shell with three separate runtime component callbacks.
-/
theorem seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_component_callbacks
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailReadSet :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailReadSetNonClobberAtRouteCI route)
    (tailDerefPointer :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailPointerDerefStabilityAtRouteCI route)
    (tailLoadReadability :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailLoadReadabilityPreservationAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_components
      hentry
      leftClosure
      (fun route =>
        { readSet := tailReadSet route
          derefPointer := tailDerefPointer route
          loadReadability := tailLoadReadability route })
      tailClosure

/- =========================================================
   Runtime-replay/component callback wrappers
   ========================================================= -/

/--
Return-aware seq closure with theorem-backed post-state preservation and an
explicit runtime replay callback.

This is the public route where post-state preservation is no longer a caller
contract; callers only provide the runtime replay contract for the selected
route.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_continuation_with_runtime_replay
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailRuntimeReplay :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailRuntimeReplayAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_replay
      hentry
      leftClosure
      tailRuntimeReplay
      tailClosure

/--
Return-aware seq closure with theorem-backed post-state preservation and named
runtime replay components.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_continuation_with_runtime_components
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailRuntimeComponents :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailRuntimeReplayComponentsAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_components
      hentry
      leftClosure
      tailRuntimeComponents
      tailClosure

/--
Return-aware seq closure with theorem-backed post-state preservation and three
separate runtime component callbacks.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_continuation_with_runtime_component_callbacks
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailReadSet :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailReadSetNonClobberAtRouteCI route)
    (tailDerefPointer :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailPointerDerefStabilityAtRouteCI route)
    (tailLoadReadability :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailLoadReadabilityPreservationAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_runtime_component_callbacks
      hentry
      leftClosure
      tailReadSet
      tailDerefPointer
      tailLoadReadability
      tailClosure

end Cpp
