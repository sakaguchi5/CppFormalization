import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyPrimitiveClosureCI
import CppFormalization.Cpp2.Closure.Internal.WhileFunctionClosureKernelCI
import CppFormalization.Cpp2.Closure.Internal.LoopBodyFunctionClosureCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverCI

`body_closure_ci_function_body_progress_or_diverges_by_cases` の
constructor-level case-driver body.

重要:
- ここでは closed theorem は作らない。
- while は同じ syntax `(.whileStmt c body)` への tail 再帰を持つので、
  case-driver 本体は明示的な recursive hypothesis を引数に取る。
- これにより、残る open surface は「この body を満たす global recursion/fixed-point を
  どう与えるか」だけになる。
-/

/-- canonical result shape, re-exported for readability at the driver level. -/
abbrev FunctionBodyCaseDriverResult (σ : State) (st : CppStmt) : Prop :=
  FunctionBodyClosureResult σ st

/-- recursive hypothesis consumed by the constructor-level case-driver body. -/
abbrev FunctionBodyCaseDriverIH : Prop :=
  ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    FunctionBodyCaseDriverResult σ st

/--
Constructor-level case-driver body for top-level function-body closure.

これは closed theorem ではなく、master shell の中身になる本体である。
seq / ite / block / while の shell surface へ分配し、
recursive hypothesis は substatement と while-tail に対してだけ使う。
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body
    (mkWhileReentry : WhileReentryReadyProvider)
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
        seq_function_body_closure_boundary_ci_honest
          hentry
          (fun hleftBoundary =>
            IH (st := s) hfragS hleftBoundary)
          (fun hty hstep =>
            seq_tail_closure_boundary_ci_of_left_normal mkWhileReentry hentry hty hstep)
          (fun _hty _hstep htailBoundary =>
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
      let hcur : WhileCurrentEntryKitCI Γ σ c body :=
        whileCurrentEntryKitCI_of_bodyClosureBoundaryCI hentry
      let htail : WhileTailBoundaryKitCI Γ σ c body :=
        whileTailBoundaryKitCI_of_bodyClosureBoundaryCI hentry
      exact
        while_function_body_closure_boundary_ci_honest
          hcur.typing
          hentry
          hcur.loopBoundary
          hcur.bodyProgressOrDiverges
          htail
          (fun {σ1} htailBoundary =>
            IH (st := .whileStmt c body) hfrag htailBoundary)
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

/-- `BodyReadyCI` entry wrapper for the constructor-level case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body
    (mkWhileReentry : WhileReentryReadyProvider)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body
      mkWhileReentry IH hfrag hentry.toClosureBoundary

end Cpp
