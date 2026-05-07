import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCoreSupportCI
import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureBoundaryCoreSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverBoundaryCoreSupportCI

Case-driver body with the sequence dependency reduced to the boundary-only core
support.

The previous pure-core-support driver accepted `SeqFunctionBodyClosureCoreSupportCI
P`, which includes both boundary and `BodyReadyCI` sequence closure surfaces.
The constructor-level driver only uses the boundary surface.  This file provides
that thinner driver shape.
-/

/--
Constructor-level case-driver body using boundary-only sequence support.

The dependencies are now split as follows:

* `P` is the pure normal-preservation core, kept as the index connecting support
  objects to the preservation service;
* `Seq` is only the boundary-level sequence closure support;
* `Wh` closes the cleaned current-boundary while step;
* `W` supplies the program-facing while backedge invariant;
* `IH` is the ordinary case-driver recursion hypothesis.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_boundaryCoreSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureBoundaryCoreSupportCI P)
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
          (fun _route htailBoundary =>
            IH (st := t) hfragT htailBoundary)
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

/-- `BodyReadyCI` wrapper for the boundary-only-support case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_boundaryCoreSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureBoundaryCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_boundaryCoreSupport
      P Seq Wh W IH hfrag hentry.toClosureBoundary

/--
Compatibility constructor for the thinner driver dependencies from the current
while-reentry implementation.
-/
def boundarySeqAndWhileCoreSupports_of_whileReentry
    (mkWhileReentry : WhileReentryReadyProvider) :
    let P := (stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry).toCore
    SeqFunctionBodyClosureBoundaryCoreSupportCI P × WhileCurrentBoundaryClosureCoreSupportCI :=
  let Pold := stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry
  (seqFunctionBodyClosureBoundaryCoreSupportCI_of_normalPreservationProvider Pold,
   whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry mkWhileReentry)

end Cpp
