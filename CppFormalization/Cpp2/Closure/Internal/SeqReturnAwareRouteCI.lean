import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareCallbacksCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI

namespace Cpp

/-!
# Closure.Internal.SeqReturnAwareRouteCI

Live return-aware route for statement sequencing.

`HeadTailReturnAwareRoutesCI` already contains the pure operational assembly:
head return returns immediately, head normal invokes the tail route, and head
divergence propagates.

The remaining issue for the existing CI seq boundary is not operational assembly.
It is witness supply: the tail boundary needs a `HasTypeStmtCI .normalK Γ s Δ`
for the actual head-normal execution.

This file makes that missing piece explicit via `normalWitness`.  That is the
right abstraction boundary: do not hide it inside a monolithic seq closure axiom.
-/

/--
Return-aware seq closure from existing seq boundary pieces plus an explicit
normal witness provider.

This theorem replaces the old semantic assembly part of
`seq_function_body_closure_boundary_ci_honest`; what remains as real debt is the
provider

`∀ hstep : BigStepStmt σ s .normal σ1, ∃ Δ, HasTypeStmtCI .normalK Γ s Δ`.

That provider should later come from a normal-control witness theorem, not from
projecting whole `returnOut` into the tail.
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
        let hw := normalWitness hstep
        match hw with
        | ⟨Δ, hty⟩ =>
            tailClosure hty hstep (tailBoundary hty hstep))

/--
`BodyReadyCI` wrapper for the return-aware seq route with explicit normal witness.
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

end Cpp
