import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverBoundaryCoreSupportCI
import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureContinuationCoreSupportCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCanonicalSeqSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverContinuationSeqSupportCI

Case-driver body whose `seq` dependency is expressed using continuation-tail
callbacks.

This is an aggressive surface migration:
- the seq dependency is no longer the old boundary-tail callback support;
- the selected post-route tail is exposed as `StmtContinuationBoundaryCI`;
- the current recursive hypothesis still consumes `BodyClosureBoundaryCI`, so
  the driver forgets the continuation boundary only at the IH call site.

That is exactly the intended transition shape: callers and support packages
speak in terms of post-state continuation boundaries, while the old IH remains
unchanged until the next recursion-interface refactor.
-/

/-- Constructor-level case-driver body using continuation-tail sequence support. -/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  cases st with
  | skip =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .skip) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | exprStmt e =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .exprStmt e) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | assign p e =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .assign p e) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | declareObj τ x ov =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .declareObj τ x ov) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | declareRef τ x p =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .declareRef τ x p) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | seq s t =>
      have hfragST : CoreBigStepFragment s ∧ CoreBigStepFragment t := by
        simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
      rcases hfragST with ⟨hfragS, hfragT⟩
      exact
        Seq.close
          hentry
          (fun hleftBoundary =>
            IH (st := s) hfragS hleftBoundary)
          (fun _route htailContinuation =>
            IH (st := t) hfragT htailContinuation.toBodyClosureBoundaryCI)
  | ite c s t =>
      have hfragST : CoreBigStepFragment s ∧ CoreBigStepFragment t := by
        simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
      rcases hfragST with ⟨hfragS, hfragT⟩
      exact
        ite_function_body_closure_boundary_ci_honest
          hentry
          (fun hthenBoundary =>
            IH (st := s) hfragS hthenBoundary)
          (fun helseBoundary =>
            IH (st := t) hfragT helseBoundary)
  | whileStmt c body =>
      exact
        while_case_driver_branch_of_coreSupport
          Wh W IH hfrag hentry
  | block ss =>
      exact
        block_function_body_closure_boundary_ci_from_opened_body
          hentry
          (fun {σ0} _hopen hopenedBoundary =>
            block_body_function_closure_boundary_ci hopenedBoundary)
  | breakStmt =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .breakStmt) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | continueStmt =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .continueStmt) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | returnStmt rv =>
      exact
        primitive_stmt_function_body_step_or_diverges_body_closure
          (st := .returnStmt rv) (by simp [PrimitiveCoreStmtConcrete]) hentry

/-- `BodyReadyCI` wrapper for the continuation-seq case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
      P Seq Wh W IH hfrag hentry.toClosureBoundary

/-- Support package whose canonical seq dependency is the continuation-tail
surface. -/
structure FunctionBodyContinuationSeqCaseDriverSupportCI : Type where
  P : StmtNormalPreservationCoreCI
  seq : SeqFunctionBodyClosureContinuationCoreSupportCI P
  whileSupport : WhileCurrentBoundaryClosureCoreSupportCI
  whileInvariant : FunctionBodyWhileBackedgeInvariantCoreProviderCI

namespace FunctionBodyContinuationSeqCaseDriverSupportCI

/-- Run the case-driver body from the continuation-seq package. -/
theorem bodyClosure
    (S : FunctionBodyContinuationSeqCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqSupport
    S.P
    S.seq
    S.whileSupport
    S.whileInvariant
    IH
    hfrag
    hentry

/-- `BodyReadyCI` wrapper for the packaged continuation-seq driver body. -/
theorem bodyReady
    (S : FunctionBodyContinuationSeqCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  S.bodyClosure IH hfrag hentry.toClosureBoundary

end FunctionBodyContinuationSeqCaseDriverSupportCI

/-- Build the continuation-seq support package from explicit continuation seq
support plus the current while supports. -/
noncomputable def functionBodyContinuationSeqCaseDriverSupportCI_of_components
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyContinuationSeqCaseDriverSupportCI :=
  { P := P
    seq := Seq
    whileSupport := Wh
    whileInvariant := W }

/-- Build the continuation-seq support package from the older boundary seq
support. -/
noncomputable def functionBodyContinuationSeqCaseDriverSupportCI_of_boundarySeqSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureBoundaryCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyContinuationSeqCaseDriverSupportCI :=
  functionBodyContinuationSeqCaseDriverSupportCI_of_components
    P
    (SeqFunctionBodyClosureContinuationCoreSupportCI.ofBoundaryCoreSupport Seq)
    Wh
    W

/-- Build the continuation-seq support package from canonical fixed-static seq
support. -/
noncomputable def functionBodyContinuationSeqCaseDriverSupportCI_of_canonicalSeqSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyContinuationSeqCaseDriverSupportCI :=
  functionBodyContinuationSeqCaseDriverSupportCI_of_boundarySeqSupport
    P
    Seq.toBoundaryCoreSupport
    Wh
    W

/-- Case-driver body from canonical fixed-static seq support, exposed through
the continuation-seq dependency surface. -/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuation
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyContinuationSeqCaseDriverSupportCI_of_canonicalSeqSupport
    P Seq Wh W).bodyClosure IH hfrag hentry

/-- `BodyReadyCI` wrapper for the continuation-exposed canonical seq driver. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuation
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport_viaContinuation
    P Seq Wh W IH hfrag hentry.toClosureBoundary

end Cpp
