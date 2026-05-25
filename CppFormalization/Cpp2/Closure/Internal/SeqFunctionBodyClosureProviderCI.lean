import CppFormalization.Cpp2.Closure.Internal.SeqReturnAwareRouteCI
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Closure.Internal.SeqNormalPreservationProviderCI

namespace Cpp

/-!
# Closure.Internal.SeqFunctionBodyClosureProviderCI

Provider-shaped public surfaces for sequence closure.

The older route-aware seq theorems take `WhileReentryReadyProvider` directly.
This file offers the same public theorem shape through
`StmtNormalPreservationProviderCI`, so callers of `seq` can talk about ordinary
normal preservation rather than while reentry.

Implementation note: the current provider still retains a compatibility
projection to while reentry, because the old underlying seq theorem has not yet
been in-place rewritten.  This is nevertheless the surface split we want: seq
now consumes a normal-preservation provider.
-/

/-- Boundary-level route-aware sequence closure through a normal-preservation provider. -/
theorem seq_function_body_closure_boundary_ci_honest_of_normalPreservationProvider
    (_P : StmtNormalPreservationProviderCI)
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
      hentry
      leftClosure
      tailClosure

/-- Route-aware wrapper name matching `SeqReturnAwareRouteCI`. -/
theorem seq_function_body_closure_boundary_ci_return_aware_of_normalPreservationProvider
    (P : StmtNormalPreservationProviderCI)
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
    seq_function_body_closure_boundary_ci_honest_of_normalPreservationProvider
      P hentry leftClosure tailClosure

/-- `BodyReadyCI` route-aware sequence closure through a normal-preservation provider. -/
theorem seq_function_body_closure_ci_honest_of_normalPreservationProvider
    (_P : StmtNormalPreservationProviderCI)
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
      hentry
      leftClosure
      tailClosure

/-- `BodyReadyCI` route-aware wrapper name matching `SeqReturnAwareRouteCI`. -/
theorem seq_function_body_closure_ci_return_aware_of_normalPreservationProvider
    (P : StmtNormalPreservationProviderCI)
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
    seq_function_body_closure_ci_honest_of_normalPreservationProvider
      P hentry leftClosure tailClosure


/- =========================================================
   Continuation-callback surfaces
   ========================================================= -/

/-- Boundary-level route-aware sequence closure through a normal-preservation
provider, with the tail callback receiving the full continuation boundary. -/
theorem seq_function_body_closure_boundary_ci_return_aware_continuation_of_normalPreservationProvider
    (_P : StmtNormalPreservationProviderCI)
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
    seq_function_body_closure_boundary_ci_return_aware_continuation
      hentry
      leftClosure
      tailClosure

/-- Alias matching the older `honest` naming surface. -/
theorem seq_function_body_closure_boundary_ci_honest_continuation_of_normalPreservationProvider
    (P : StmtNormalPreservationProviderCI)
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
    seq_function_body_closure_boundary_ci_return_aware_continuation_of_normalPreservationProvider
      P hentry leftClosure tailClosure

/-- `BodyReadyCI` route-aware sequence closure through a normal-preservation
provider, with the tail callback receiving the full continuation boundary. -/
theorem seq_function_body_closure_ci_return_aware_continuation_of_normalPreservationProvider
    (_P : StmtNormalPreservationProviderCI)
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
    seq_function_body_closure_ci_return_aware_continuation
      hentry
      leftClosure
      tailClosure

/-- Alias matching the older `honest` naming surface. -/
theorem seq_function_body_closure_ci_honest_continuation_of_normalPreservationProvider
    (P : StmtNormalPreservationProviderCI)
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
    seq_function_body_closure_ci_return_aware_continuation_of_normalPreservationProvider
      P hentry leftClosure tailClosure

end Cpp
