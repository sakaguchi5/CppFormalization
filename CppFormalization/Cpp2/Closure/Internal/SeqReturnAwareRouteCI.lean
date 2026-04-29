import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI

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

end Cpp
