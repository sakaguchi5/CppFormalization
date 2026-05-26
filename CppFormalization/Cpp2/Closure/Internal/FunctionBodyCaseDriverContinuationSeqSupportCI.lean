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

/-- Mainline-facing primitive statement closure support.

The older case-driver closes primitive statements by directly calling
`primitive_stmt_function_body_step_or_diverges_body_closure`, which depends on
the current concrete-refined primitive axiom.  This package makes that dependency
explicit, so the mainline root does not hide primitive debt.
-/
structure FunctionBodyPrimitiveClosureSupportCI : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      PrimitiveCoreStmtConcrete st →
      BodyClosureBoundaryCI Γ σ st →
      FunctionBodyCaseDriverResult σ st

/-- Compatibility primitive support using the current concrete-refined route.

Keep this out of the mainline audit root unless you intentionally want to count
the old primitive concrete axiom as supplied evidence.
-/
def functionBodyPrimitiveClosureSupportCI_of_currentPrimitiveRoute :
    FunctionBodyPrimitiveClosureSupportCI :=
  { close := fun hprim hentry =>
      primitive_stmt_function_body_step_or_diverges_body_closure
        hprim hentry }


/-- Mainline-facing block closure support.

The older continuation-seq case driver closes the `block` branch by calling
`block_body_function_closure_boundary_ci` directly.  That immediately pulls the
old concrete/block-cons route into every mainline audit.

This package makes the block dependency explicit.  The mainline continuation
root can now say: seq and while are supplied by their current continuation
surfaces, and block closure is a separate dependency.  This does not solve block;
it prevents the function-body root from hiding the old block route.
-/
structure FunctionBodyBlockClosureSupportCI : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock},
      BodyClosureBoundaryCI Γ σ (.block ss) →
      FunctionBodyCaseDriverResult σ (.block ss)

/-- Compatibility block support using the current old block route.

Keep this out of the mainline root when auditing.  It is provided only so that
old callers can be migrated gradually.
-/
def functionBodyBlockClosureSupportCI_of_currentBlockRoute :
    FunctionBodyBlockClosureSupportCI :=
  { close := fun hentry =>
      block_function_body_closure_boundary_ci_from_opened_body
        hentry
        (fun _hopen hopenedBoundary =>
          block_body_function_closure_boundary_ci hopenedBoundary) }


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

/-- Constructor-level case-driver body using continuation-tail sequence support and
an explicit block support.

This is the preferred audit surface after the continuation-root migration:
the `block` branch no longer directly imports the old block-body closure route.
Any remaining block debt is now visible as an explicit parameter.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
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
      exact Block.close hentry
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

/-- Constructor-level case-driver body using explicit primitive, continuation-seq,
and block support.

This is now the preferred audit surface:
- primitive closure is supplied explicitly;
- seq tail closure is supplied through continuation support;
- block closure is supplied explicitly;
- while closure support and invariant are explicit.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockPrimitiveSupport
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  cases st with
  | skip =>
      exact Primitive.close (st := .skip) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | exprStmt e =>
      exact Primitive.close (st := .exprStmt e) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | assign p e =>
      exact Primitive.close (st := .assign p e) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | declareObj τ x ov =>
      exact Primitive.close (st := .declareObj τ x ov) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | declareRef τ x p =>
      exact Primitive.close (st := .declareRef τ x p) (by simp [PrimitiveCoreStmtConcrete]) hentry
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
      exact Block.close hentry
  | breakStmt =>
      exact Primitive.close (st := .breakStmt) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | continueStmt =>
      exact Primitive.close (st := .continueStmt) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | returnStmt rv =>
      exact Primitive.close (st := .returnStmt rv) (by simp [PrimitiveCoreStmtConcrete]) hentry

/-- `BodyReadyCI` wrapper for the primitive/continuation-seq/block-support case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockPrimitiveSupport
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockPrimitiveSupport
      Primitive P Seq Wh W Block IH hfrag hentry.toClosureBoundary


/-- `BodyReadyCI` wrapper for the continuation-seq/block-support case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockSupport
      P Seq Wh W Block IH hfrag hentry.toClosureBoundary


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

/-- Support package whose dependencies are primitive support, continuation seq
support, and explicit block support.

This is the most audit-friendly package currently available: it does not hide
primitive or block concrete routes inside the constructor-level case driver.
-/
structure FunctionBodyContinuationSeqBlockPrimitiveCaseDriverSupportCI : Type where
  primitiveSupport : FunctionBodyPrimitiveClosureSupportCI
  P : StmtNormalPreservationCoreCI
  seq : SeqFunctionBodyClosureContinuationCoreSupportCI P
  whileSupport : WhileCurrentBoundaryClosureCoreSupportCI
  whileInvariant : FunctionBodyWhileBackedgeInvariantCoreProviderCI
  blockSupport : FunctionBodyBlockClosureSupportCI

namespace FunctionBodyContinuationSeqBlockPrimitiveCaseDriverSupportCI

/-- Run the case-driver body from the primitive/continuation-seq/block package. -/
theorem bodyClosure
    (S : FunctionBodyContinuationSeqBlockPrimitiveCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockPrimitiveSupport
    S.primitiveSupport
    S.P
    S.seq
    S.whileSupport
    S.whileInvariant
    S.blockSupport
    IH
    hfrag
    hentry

/-- `BodyReadyCI` wrapper for the packaged primitive/continuation-seq/block driver body. -/
theorem bodyReady
    (S : FunctionBodyContinuationSeqBlockPrimitiveCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  S.bodyClosure IH hfrag hentry.toClosureBoundary

end FunctionBodyContinuationSeqBlockPrimitiveCaseDriverSupportCI

/-- Build the audit-friendly primitive/continuation-seq/block support package
from components. -/
noncomputable def functionBodyContinuationSeqBlockPrimitiveCaseDriverSupportCI_of_components
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI) :
    FunctionBodyContinuationSeqBlockPrimitiveCaseDriverSupportCI :=
  { primitiveSupport := Primitive
    P := P
    seq := Seq
    whileSupport := Wh
    whileInvariant := W
    blockSupport := Block }


/-- Support package whose dependencies are continuation seq support plus explicit
block support.

This is the audit-friendly package.  Unlike
`FunctionBodyContinuationSeqCaseDriverSupportCI`, it does not hide the old block
route inside the constructor-level driver.
-/
structure FunctionBodyContinuationSeqBlockCaseDriverSupportCI : Type where
  P : StmtNormalPreservationCoreCI
  seq : SeqFunctionBodyClosureContinuationCoreSupportCI P
  whileSupport : WhileCurrentBoundaryClosureCoreSupportCI
  whileInvariant : FunctionBodyWhileBackedgeInvariantCoreProviderCI
  blockSupport : FunctionBodyBlockClosureSupportCI

namespace FunctionBodyContinuationSeqBlockCaseDriverSupportCI

/-- Run the case-driver body from the continuation-seq/block package. -/
theorem bodyClosure
    (S : FunctionBodyContinuationSeqBlockCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqBlockSupport
    S.P
    S.seq
    S.whileSupport
    S.whileInvariant
    S.blockSupport
    IH
    hfrag
    hentry

/-- `BodyReadyCI` wrapper for the packaged continuation-seq/block driver body. -/
theorem bodyReady
    (S : FunctionBodyContinuationSeqBlockCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  S.bodyClosure IH hfrag hentry.toClosureBoundary

end FunctionBodyContinuationSeqBlockCaseDriverSupportCI

/-- Build the audit-friendly continuation-seq/block support package from
components. -/
noncomputable def functionBodyContinuationSeqBlockCaseDriverSupportCI_of_components
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI) :
    FunctionBodyContinuationSeqBlockCaseDriverSupportCI :=
  { P := P
    seq := Seq
    whileSupport := Wh
    whileInvariant := W
    blockSupport := Block }


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
