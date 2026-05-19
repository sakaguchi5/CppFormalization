import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI
import CppFormalization.Cpp2.Closure.Internal.SeqRuntimeReplayRouteCI
import CppFormalization.Cpp2.Continuation.Boundary.Body

namespace Cpp

/-!
# Closure.Internal.SeqReturnAwareRouteCI

Live return-aware route for statement sequencing.

This file exposes route-aware theorem-backed wrappers as its canonical public
surface. The older explicit-provider and explicit-tail-boundary compatibility
adapters have been removed from this file; callers should enter the tail through
the selected `SeqHeadNormalRouteCI`.
-/

/--
Route-aware theorem-backed return-aware seq closure.

This is the canonical boundary-level surface.  The tail callback receives the
selected head-normal route and the boundary at `route.Θ`.
-/
theorem seq_function_body_closure_boundary_ci_return_aware
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyClosureBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest
      mkWhileReentry hentry leftClosure tailClosure

/-- Route-aware theorem-backed `BodyReadyCI` wrapper. -/
theorem seq_function_body_closure_ci_return_aware
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry.toClosureBoundary).profile) →
        BodyReadyCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_ci_honest
      mkWhileReentry
      hentry
      leftClosure
      tailClosure


/- =========================================================
   Continuation-callback route-aware wrappers
   ========================================================= -/

/-- Route-aware theorem-backed seq closure with a full continuation callback.

This is a surface-level refactoring wrapper: internally it reuses the existing
`BodyClosureBoundaryCI` route, but the user-facing tail callback receives the
new continuation boundary shape.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_continuation
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_return_aware
      mkWhileReentry
      hentry
      leftClosure
      (fun route htail =>
        tailClosure route
          (StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI htail))

/-- `BodyReadyCI` wrapper with a full continuation callback. -/
theorem seq_function_body_closure_ci_return_aware_continuation
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry.toClosureBoundary).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_ci_return_aware
      mkWhileReentry
      hentry
      leftClosure
      (fun route htail =>
        tailClosure route
          (StmtContinuationBoundaryCI.ofBodyReadyCI htail))

/- =========================================================
   Explicit stability-callback wrappers
   ========================================================= -/

/--
Return-aware seq closure with an explicit route-local tail stability callback.

This is the public wrapper closest to the intended final shape:
callers provide the selected route, prove that this route leaves the tail
dynamically enterable, and then receive a full post-state continuation boundary.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_continuation_with_stability
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailStability :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailStabilityAtRouteCI route)
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
      tailStability
      tailClosure

/--
Body-boundary compatibility wrapper for the explicit route-stability surface.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_with_stability
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailStability :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailStabilityAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyClosureBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_with_stability
      hentry
      leftClosure
      tailStability
      tailClosure


/-- 
Return-aware seq closure with post-state and runtime replay supplied separately.

This is the most decomposed public surface at this stage.  Static/name-scope
data is read from the selected route; callers only provide the two genuinely
dynamic pieces that remain visible now:

* post-state/environment preservation;
* runtime replay/readiness of the tail.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_continuation_with_replay_parts
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailPostState :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailPostStateAtRouteCI route)
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
    seq_function_body_closure_boundary_ci_return_aware_continuation_with_stability
      hentry
      leftClosure
      (fun route =>
        seq_tail_stability_at_route_ci_of_parts
          route
          (tailPostState route)
          (tailRuntimeReplay route))
      tailClosure

/--
Body-boundary compatibility wrapper for the post-state/runtime-replay split.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_with_replay_parts
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailPostState :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailPostStateAtRouteCI route)
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
    seq_function_body_closure_boundary_ci_return_aware_with_stability
      hentry
      leftClosure
      (fun route =>
        seq_tail_stability_at_route_ci_of_parts
          route
          (tailPostState route)
          (tailRuntimeReplay route))
      tailClosure

end Cpp
