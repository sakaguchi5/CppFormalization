import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverContinuationSeqSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverContinuationIHCI

Continuation-boundary recursive hypothesis for the function-body case driver.

The previous driver IH consumes `BodyClosureBoundaryCI`.  That is still usable,
but it keeps the recursion interface tied to the old closure-boundary surface.

This file introduces the next surface:

`FunctionBodyContinuationCaseDriverIH`

which consumes `StmtContinuationBoundaryCI`.  During the transition, this IH can
be forgotten back to the old `FunctionBodyCaseDriverIH` by converting a
`BodyClosureBoundaryCI` into a continuation boundary.  The important design
move is that new call sites can now state the recursive demand in terms of
post-state continuation boundaries.
-/

/-- Recursive hypothesis whose entry boundary is the full statement continuation
boundary. -/
abbrev FunctionBodyContinuationCaseDriverIH : Prop :=
  ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
    CoreBigStepFragment st →
    StmtContinuationBoundaryCI Γ σ st →
    FunctionBodyCaseDriverResult σ st

namespace FunctionBodyContinuationCaseDriverIH

/-- Forget a continuation-boundary IH to the old closure-boundary IH.

This is the transitional adapter.  It should eventually become unnecessary once
the constructor-level driver directly consumes continuation boundaries in every
branch.
-/
def toBoundaryIH
    (IH : FunctionBodyContinuationCaseDriverIH) :
    FunctionBodyCaseDriverIH :=
  fun {Γ σ st} hfrag hentry =>
    IH (Γ := Γ) (σ := σ) (st := st) hfrag
      (StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI hentry)

end FunctionBodyContinuationCaseDriverIH

/-- Constructor-level case-driver body with a continuation-boundary entry and a
continuation-boundary recursive hypothesis.

Internally this still reuses the continuation-seq support driver by adapting the
IH to the old boundary surface.  The public recursion surface is nevertheless
now the continuation boundary.
-/
theorem body_continuation_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : StmtContinuationBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    P
    Seq
    Wh
    W
    IH.toBoundaryIH
    hfrag
    hentry.toBodyClosureBoundaryCI

/-- Closure-boundary wrapper for the continuation-IH driver. -/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationIH
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_continuation_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    P
    Seq
    Wh
    W
    IH
    hfrag
    (StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI hentry)

/-- Ready-entry wrapper for the continuation-IH driver. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_continuationIH
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_continuation_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    P
    Seq
    Wh
    W
    IH
    hfrag
    (StmtContinuationBoundaryCI.ofBodyReadyCI hentry)

namespace FunctionBodyContinuationSeqCaseDriverSupportCI

/-- Run the continuation-seq package with a continuation-boundary IH and a
continuation-boundary entry. -/
theorem bodyContinuation
    (S : FunctionBodyContinuationSeqCaseDriverSupportCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : StmtContinuationBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_continuation_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    S.P
    S.seq
    S.whileSupport
    S.whileInvariant
    IH
    hfrag
    hentry

/-- Closure-boundary entry wrapper for the continuation-IH package runner. -/
theorem bodyClosureContinuationIH
    (S : FunctionBodyContinuationSeqCaseDriverSupportCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  S.bodyContinuation IH hfrag
    (StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI hentry)

/-- Ready-entry wrapper for the continuation-IH package runner. -/
theorem bodyReadyContinuationIH
    (S : FunctionBodyContinuationSeqCaseDriverSupportCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  S.bodyContinuation IH hfrag
    (StmtContinuationBoundaryCI.ofBodyReadyCI hentry)

end FunctionBodyContinuationSeqCaseDriverSupportCI

/-- Case-driver body from canonical fixed-static seq support, exposed through
both continuation-seq support and continuation-boundary IH. -/
theorem body_continuation_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuationIH
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : StmtContinuationBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyContinuationSeqCaseDriverSupportCI_of_canonicalSeqSupport
    P Seq Wh W).bodyContinuation IH hfrag hentry

/-- Closure-boundary wrapper for the canonical continuation-IH driver. -/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuationIH
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_continuation_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuationIH
    P Seq Wh W IH hfrag
    (StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI hentry)

/-- Ready-entry wrapper for the canonical continuation-IH driver. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuationIH
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_continuation_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuationIH
    P Seq Wh W IH hfrag
    (StmtContinuationBoundaryCI.ofBodyReadyCI hentry)

end Cpp
