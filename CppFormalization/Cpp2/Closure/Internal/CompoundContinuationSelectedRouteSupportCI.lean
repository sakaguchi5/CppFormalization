import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureContinuationCoreSupportCI
import CppFormalization.Cpp2.Continuation.Boundary.Seq
import CppFormalization.Cpp2.Continuation.Boundary.Cons
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Tail.Continuation
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Tail.Continuation

namespace Cpp

/-!
# Closure.Internal.CompoundContinuationSelectedRouteSupportCI

Selected-route bridge layer from `CompoundContinuation` into the existing
closure/case-driver continuation surfaces.

This file deliberately does not delete or rewrite the legacy exact-tail
constructors.  It adds an upstream path:

```text
CompoundContinuation continuation input
  → StmtContinuationBoundaryCI / BlockContinuationDynamicBoundary
  → existing closure / case-driver continuation callbacks
```

The intended direction is to let selected-route closure code depend on
post-state preservation + replay, rather than on broad readiness transport.
-/

/-- Materialize a full seq tail continuation boundary from CompoundContinuation. -/
noncomputable def seq_tail_stmt_continuation_boundary_ci_of_compoundContinuation
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (input : CompoundContinuation.Seq.Tail.ContinuationInput route.toCore) :
    StmtContinuationBoundaryCI route.Θ σ1 t :=
  seq_tail_continuation_boundary_ci_of_compound_continuation
    hentry route input

/-- Compatibility view as an ordinary body closure boundary for the seq tail. -/
noncomputable def seq_tail_body_closure_boundary_ci_of_compoundContinuation
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (input : CompoundContinuation.Seq.Tail.ContinuationInput route.toCore) :
    BodyClosureBoundaryCI route.Θ σ1 t :=
  (seq_tail_stmt_continuation_boundary_ci_of_compoundContinuation
    hentry route input).toBodyClosureBoundaryCI

/-- Compatibility view as `BodyReadyCI` for existing IH call sites. -/
noncomputable def seq_tail_body_ready_ci_of_compoundContinuation
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (input : CompoundContinuation.Seq.Tail.ContinuationInput route.toCore) :
    BodyReadyCI route.Θ σ1 t :=
  (seq_tail_stmt_continuation_boundary_ci_of_compoundContinuation
    hentry route input).toBodyReadyCI

/--
A seq closure support surface whose tail callback receives the new
CompoundContinuation input instead of a prebuilt continuation boundary.

This is a new upstream surface.  It is intentionally not inter-converted from
`SeqFunctionBodyClosureContinuationCoreSupportCI`, because an arbitrary
`StmtContinuationBoundaryCI` does not contain the replay witness required by
`CompoundContinuation.Seq.Tail.ContinuationInput`.
-/
structure SeqFunctionBodyClosureCompoundContinuationCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s) →
      (∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        CompoundContinuation.Seq.Tail.ContinuationInput route.toCore →
        FunctionBodyClosureResult σ1 t) →
      FunctionBodyClosureResult σ (.seq s t)

namespace SeqFunctionBodyClosureCompoundContinuationCoreSupportCI

/--
Apply the CompoundContinuation seq support surface.

This wrapper is intentionally small; the new support package itself decides how
to obtain the route-local continuation input.
-/
theorem apply
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqFunctionBodyClosureCompoundContinuationCoreSupportCI P)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        CompoundContinuation.Seq.Tail.ContinuationInput route.toCore →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) :=
  Seq.close hentry leftClosure tailClosure

end SeqFunctionBodyClosureCompoundContinuationCoreSupportCI

/--
Cons dynamic continuation boundary from CompoundContinuation, exposed from the
Closure/Internal side for case-driver/block-tail migration.

The input route is the operational core route at the tail environment `Θ`.
-/
def cons_tail_block_continuation_dynamic_boundary_of_compoundContinuation
    {Γ Θ : TypeEnv} {σ σ1 : State} {s : CppStmt} {ss : StmtBlock}
    (hhead : HasTypeStmtCI .normalK Γ s Θ)
    (route : CompoundContinuation.Cons.HeadNormalRouteCore Θ σ σ1 s ss)
    (input : CompoundContinuation.Cons.Tail.ContinuationInput route) :
    BlockContinuationDynamicBoundary Θ σ1 ss :=
  (cons_normal_continuation_dynamic_of_compound_continuation
    hhead route input).tail

/-- Compatibility projection to post-state + block-tail readiness. -/
theorem cons_tail_ready_of_compoundContinuation
    {Γ Θ : TypeEnv} {σ σ1 : State} {s : CppStmt} {ss : StmtBlock}
    (hhead : HasTypeStmtCI .normalK Γ s Θ)
    (route : CompoundContinuation.Cons.HeadNormalRouteCore Θ σ σ1 s ss)
    (input : CompoundContinuation.Cons.Tail.ContinuationInput route) :
    ScopedTypedStateConcrete Θ σ1 ∧ BlockReadyConcrete Θ σ1 ss := by
  let hcont :=
    cons_normal_continuation_dynamic_of_compound_continuation
      hhead route input
  exact ⟨hcont.postState, hcont.tailReady⟩

end Cpp
