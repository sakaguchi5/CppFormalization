import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureBoundaryCoreSupportCI

namespace Cpp

/-!
# Closure.Internal.SeqFunctionBodyClosureBoundaryDirectCoreSupportCI

A direct assembly layer for boundary-level route-aware sequence closure.

The previous `SeqFunctionBodyClosureBoundaryCoreSupportCI` is already the right
caller-facing dependency for the case driver, but its compatibility constructor
still obtains the support by calling the older `seq_function_body_closure...`
theorem.  This file exposes the smaller ingredients needed to build that support
without mentioning while reentry or the old seq theorem.

C++ reading: to close `s; t` as a function body, we need exactly:

1. a boundary for the head statement `s`;
2. for every actual head-normal execution, the selected normal route and a
   boundary for the tail `t` at the routed post-environment/state.

The operational return-aware assembly itself is theorem-backed by
`seq_function_body_result_return_aware`.
-/

/--
The direct boundary ingredients for route-aware sequence closure.

`P` is the pure normal-preservation core that this support is meant to be built
against.  The fields are intentionally the two non-operational boundary pieces:

* `leftBoundary` extracts the closure boundary for the head;
* `tailRouteBoundary` reconstructs the routed tail boundary after an actual
  head-normal step.

The final function-body result is assembled separately and theoremically.
-/
structure SeqFunctionBodyClosureBoundaryDirectCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  leftBoundary :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      BodyClosureBoundaryCI Γ σ (.seq s t) →
      BodyClosureBoundaryCI Γ σ s

  tailRouteBoundary :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      BigStepStmt σ s .normal σ1 →
      Σ route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile,
        BodyClosureBoundaryCI route.Θ σ1 t

/--
Assemble boundary-only sequence support from direct head/tail boundary support.

This is the first seq closure implementation layer that does not call the older
`seq_function_body_closure_boundary_ci_honest` theorem.  The only operational
assembly step is `seq_function_body_result_return_aware`.
-/
def seqFunctionBodyClosureBoundaryCoreSupportCI_of_direct
    {P : StmtNormalPreservationCoreCI}
    (D : SeqFunctionBodyClosureBoundaryDirectCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  { close := by
      intro Γ σ s t hentry leftClosure tailClosure
      exact
        seq_function_body_result_return_aware
          (leftClosure (D.leftBoundary hentry))
          (tailAfterHeadNormal := by
            intro σ1 hstepHead
            rcases D.tailRouteBoundary hentry hstepHead with ⟨route, htailBoundary⟩
            exact tailClosure route htailBoundary) }

/--
Readable theorem wrapper for direct sequence closure support.
-/
theorem seq_function_body_closure_boundary_ci_of_directCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (D : SeqFunctionBodyClosureBoundaryDirectCoreSupportCI P)
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
    FunctionBodyClosureResult σ (.seq s t) :=
  (seqFunctionBodyClosureBoundaryCoreSupportCI_of_direct D).close
    hentry leftClosure tailClosure

end Cpp
