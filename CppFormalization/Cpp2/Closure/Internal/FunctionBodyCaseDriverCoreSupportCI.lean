import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCI
import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureCoreSupportCI
import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryClosureCoreSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverCoreSupportCI

Case-driver body with `seq` and `while` both entering through clean support
objects.

Compared with `FunctionBodyCaseDriverProviderCI`, this layer removes the need for
`StmtNormalPreservationProviderCI.toWhileReentryReadyProvider` at the driver
surface.  The driver receives:

- `P : StmtNormalPreservationCoreCI`, the pure normal-preservation service;
- `Seq : SeqFunctionBodyClosureCoreSupportCI P`, implementation support for seq;
- `Wh : WhileCurrentBoundaryClosureCoreSupportCI`, implementation support for while;
- `W : FunctionBodyWhileBackedgeInvariantCoreProviderCI`, the program-facing
  while backedge invariant provider.

Any old while-reentry implementation is now pushed into construction of `Seq`
and `Wh`, not into the case driver itself.
-/

/-- Provider for the program-facing while backedge invariant used by the driver. -/
structure FunctionBodyWhileBackedgeInvariantCoreProviderCI : Type where
  invariant :
    ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt},
      CoreBigStepFragment (.whileStmt c body) →
      BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
      WhileBackedgeInvariantCI Γ c body

/-- Build the tail-closure shell from the case-driver recursive hypothesis. -/
def whileTailClosureShellCI_of_caseDriverIH_core
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body)) :
    WhileTailClosureShellCI Γ c body :=
  { close := by
      intro σ1 htailBoundary
      exact IH (st := .whileStmt c body) hfrag htailBoundary }

/-- The while branch through the clean closure-step support. -/
theorem while_case_driver_branch_of_coreSupport
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body))
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    FunctionBodyCaseDriverResult σ (.whileStmt c body) := by
  exact
    Wh.close
      hentry
      { invariant := W.invariant hfrag hentry
        tail := whileTailClosureShellCI_of_caseDriverIH_core IH hfrag }

/--
Constructor-level case-driver body using pure-core seq/while support.

This is the driver shape we want long-term: `seq` consumes normal preservation
via `Seq`, while `while` consumes a closure-step support plus the explicit
backedge invariant provider.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_coreSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureCoreSupportCI P)
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
        Seq.closeBoundary
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

/-- `BodyReadyCI` entry wrapper for the pure-core-support case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_coreSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_coreSupport
      P Seq Wh W IH hfrag hentry.toClosureBoundary

/--
Compatibility constructor for the new driver dependencies from the current
while-reentry implementation.
-/
def seqAndWhileCoreSupports_of_whileReentry
    (mkWhileReentry : WhileReentryReadyProvider) :
    let P := (stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry).toCore
    SeqFunctionBodyClosureCoreSupportCI P × WhileCurrentBoundaryClosureCoreSupportCI :=
  let Pold := stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry
  (seqFunctionBodyClosureCoreSupportCI_of_normalPreservationProvider Pold,
   whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry mkWhileReentry)

end Cpp
