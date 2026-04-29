import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareCallbacksCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI

namespace Cpp

/-!
# Closure.Internal.SeqReturnAwareRouteCI

Live return-aware route for statement sequencing.

The `normalWitness` callback introduced earlier is now theorem-backed by
`seq_left_normalWitness_of_entry` in `FunctionBodyCaseSplitCI`.

This file exposes route-aware theorem-backed wrappers as its canonical public
surface. Explicit-provider and explicit-tail-boundary compatibility adapters
are isolated under `SeqLegacy`; new code should not call them directly.
-/

namespace SeqLegacy

/--
Legacy return-aware seq closure from existing seq boundary pieces plus an
explicit normal witness provider.

Prefer `seq_function_body_closure_boundary_ci_return_aware` below when working
from a `BodyClosureBoundaryCI`.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_with_normalWitness
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (normalWitness :
      ∀ {σ1 : State},
        BigStepStmt σ s .normal σ1 →
        ∃ Δ, HasTypeStmtCI .normalK Γ s Δ)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  have hleft : FunctionBodyClosureResult σ s :=
    leftClosure (seq_left_closure_boundary_ci_of_entry hentry)
  exact
    seq_function_body_closure_boundary_ci_return_aware_from_callbacks
      hentry
      hleft
      (fun hstep =>
        match normalWitness hstep with
        | ⟨Δ, hty⟩ =>
            tailClosure hty hstep (tailBoundary hty hstep))

end SeqLegacy

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

namespace SeqLegacy

/--
Legacy explicit-tail-boundary compatibility surface.

The normal witness provider is no longer a callback, but this still accepts the
old arbitrary-`Δ` tail boundary callback shape for migration. Prefer
`seq_function_body_closure_boundary_ci_return_aware` for new code.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_with_tail_boundary
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_with_tail_boundary
      hentry leftClosure tailBoundary tailClosure

end SeqLegacy

namespace SeqLegacy

/--
Legacy `BodyReadyCI` wrapper for the return-aware seq route with explicit normal
witness.
-/
theorem seq_function_body_closure_ci_return_aware_with_normalWitness
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (normalWitness :
      ∀ {σ1 : State},
        BigStepStmt σ s .normal σ1 →
        ∃ Δ, HasTypeStmtCI .normalK Γ s Δ)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_return_aware_with_normalWitness
      hentry.toClosureBoundary
      (fun hleftBoundary => leftClosure hleftBoundary.toBodyReadyCI)
      normalWitness
      (fun hty hstep => (tailBoundary hty hstep).toClosureBoundary)
      (fun hty hstep htailBoundary =>
        tailClosure hty hstep htailBoundary.toBodyReadyCI)

end SeqLegacy

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

namespace SeqLegacy

/-- Legacy explicit-tail-boundary compatibility `BodyReadyCI` wrapper. -/
theorem seq_function_body_closure_ci_return_aware_with_tail_boundary
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_return_aware_with_tail_boundary
      hentry.toClosureBoundary
      (fun hleftBoundary => leftClosure hleftBoundary.toBodyReadyCI)
      (fun hty hstep => (tailBoundary hty hstep).toClosureBoundary)
      (fun hty hstep htailBoundary =>
        tailClosure hty hstep htailBoundary.toBodyReadyCI)

end SeqLegacy


end Cpp
