import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCI
import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureProviderCI
import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryClosureStepCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverProviderCI

Case-driver body with the `seq` branch depending on
`StmtNormalPreservationProviderCI` rather than directly on
`WhileReentryReadyProvider`.

The while branch is also routed through the cleaned current-boundary closure-step
surface.  It still uses the provider's compatibility projection to while reentry
because the current while theorem itself is built on `WhileReentryReadyProvider`.
-/

/-- Provider for the program-facing while backedge invariant used by the driver. -/
structure FunctionBodyWhileBackedgeInvariantProviderCI : Type where
  invariant :
    ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt},
      CoreBigStepFragment (.whileStmt c body) →
      BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
      WhileBackedgeInvariantCI Γ c body

/-- Build the tail-closure shell from the case-driver recursive hypothesis. -/
def whileTailClosureShellCI_of_caseDriverIH
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body)) :
    WhileTailClosureShellCI Γ c body :=
  { close := by
      intro σ1 htailBoundary
      exact IH (st := .whileStmt c body) hfrag htailBoundary }

/-- The while branch through the cleaned closure-step route. -/
theorem while_case_driver_branch_of_closureStep
    (W : FunctionBodyWhileBackedgeInvariantProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body))
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    FunctionBodyCaseDriverResult σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_closureStep
      hentry
      { invariant := W.invariant hfrag hentry
        tail := whileTailClosureShellCI_of_caseDriverIH IH hfrag }


/--
Constructor-level case-driver body using the provider-shaped seq surface.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_provider
    (P : StmtNormalPreservationProviderCI)
    (W : FunctionBodyWhileBackedgeInvariantProviderCI)
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
        seq_function_body_closure_boundary_ci_honest_of_normalPreservationProvider
          P
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
        while_case_driver_branch_of_closureStep
          W IH hfrag hentry
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

/-- `BodyReadyCI` entry wrapper for the provider-shaped case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_provider
    (P : StmtNormalPreservationProviderCI)
    (W : FunctionBodyWhileBackedgeInvariantProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_provider
      P W IH hfrag hentry.toClosureBoundary

end Cpp
