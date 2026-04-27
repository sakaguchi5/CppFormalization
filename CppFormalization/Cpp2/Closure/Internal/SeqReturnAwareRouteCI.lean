import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareCallbacksCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI

namespace Cpp

/-!
# Closure.Internal.SeqReturnAwareRouteCI

Live return-aware route for statement sequencing.

The `normalWitness` callback introduced earlier is now theorem-backed by
`seq_left_normalWitness_of_entry` in `FunctionBodyCaseSplitCI`.

This file keeps the old explicit-provider route for compatibility and exposes
the theorem-backed wrapper below.
-/

/--
Return-aware seq closure from existing seq boundary pieces plus an explicit
normal witness provider.

Compatibility theorem.  Prefer
`seq_function_body_closure_boundary_ci_return_aware` below when working from a
`BodyClosureBoundaryCI`.
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

/--
Theorem-backed return-aware seq closure.

This is the intended replacement surface: the normal witness provider is no
longer a callback.  It is obtained from the left-boundary adequacy via
`seq_left_normalWitness_of_entry`.
-/
theorem seq_function_body_closure_boundary_ci_return_aware
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
    seq_function_body_closure_boundary_ci_honest
      hentry leftClosure tailBoundary tailClosure

/--
`BodyReadyCI` wrapper for the return-aware seq route with explicit normal witness.
Compatibility theorem.
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

/-- Theorem-backed `BodyReadyCI` wrapper. -/
theorem seq_function_body_closure_ci_return_aware
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
    seq_function_body_closure_boundary_ci_return_aware
      hentry.toClosureBoundary
      (fun hleftBoundary => leftClosure hleftBoundary.toBodyReadyCI)
      (fun hty hstep => (tailBoundary hty hstep).toClosureBoundary)
      (fun hty hstep htailBoundary =>
        tailClosure hty hstep htailBoundary.toBodyReadyCI)

end Cpp
