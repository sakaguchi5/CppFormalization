import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureContinuationDataSupportCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCI
import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryClosureCoreSupportCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCoreSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverContinuationSeqSupportCI

Data-backed mainline case-driver body.

This file intentionally keeps only the current mainline shape:
- primitive closure is explicit;
- `ite` closure is explicit;
- seq slot-selection data is explicit;
- seq continuation support is data-backed;
- while support/invariant are explicit;
- block closure is explicit.

The old continuationSeq / continuationSeqBlock / continuationSeqBlockPrimitive /
continuationSeqBlockPrimitiveIte surfaces are removed here.  If a downstream file
still needs one of those names, that file is part of the old route tree and
should be removed or rewritten to the data-backed surface.
-/

/-- Mainline-facing provider of Type-level seq slot-selection data. -/
structure FunctionBodySeqSlotSelectionDataSupportCI : Type where
  select :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      SeqLeftSlotSelectionDataCI hentry

/-- Mainline-facing `ite` closure support. -/
structure FunctionBodyIteClosureSupportCI : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt},
      BodyClosureBoundaryCI Γ σ (.ite c s t) →
      (BodyClosureBoundaryCI Γ σ s → FunctionBodyCaseDriverResult σ s) →
      (BodyClosureBoundaryCI Γ σ t → FunctionBodyCaseDriverResult σ t) →
      FunctionBodyCaseDriverResult σ (.ite c s t)

/-- Compatibility `ite` support using the current branch-boundary route. -/
def functionBodyIteClosureSupportCI_of_currentIteRoute :
    FunctionBodyIteClosureSupportCI :=
  { close := fun hentry thenClosure elseClosure =>
      ite_function_body_closure_boundary_ci_honest
        hentry
        thenClosure
        elseClosure }

/-- Mainline-facing primitive statement closure support. -/
structure FunctionBodyPrimitiveClosureSupportCI : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      PrimitiveCoreStmtConcrete st →
      BodyClosureBoundaryCI Γ σ st →
      FunctionBodyCaseDriverResult σ st

/-- Compatibility primitive support using the current concrete-refined route. -/
def functionBodyPrimitiveClosureSupportCI_of_currentPrimitiveRoute :
    FunctionBodyPrimitiveClosureSupportCI :=
  { close := fun hprim hentry =>
      primitive_stmt_function_body_step_or_diverges_body_closure
        hprim hentry }

/-- Mainline-facing block closure support. -/
structure FunctionBodyBlockClosureSupportCI : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock},
      BodyClosureBoundaryCI Γ σ (.block ss) →
      FunctionBodyCaseDriverResult σ (.block ss)

/-- Compatibility block support using the current old block route. -/
def functionBodyBlockClosureSupportCI_of_currentBlockRoute :
    FunctionBodyBlockClosureSupportCI :=
  { close := fun hentry =>
      block_function_body_closure_boundary_ci_from_opened_body
        hentry
        (fun _hopen hopenedBoundary =>
          block_body_function_closure_boundary_ci hopenedBoundary) }

/-- Constructor-level case-driver body using data-backed seq support. -/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqDataBlockPrimitiveIteSupport
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (Ite : FunctionBodyIteClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (SeqSlots : FunctionBodySeqSlotSelectionDataSupportCI)
    (Seq : SeqFunctionBodyClosureContinuationDataSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  cases st with
  | skip => exact Primitive.close (st := .skip) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | exprStmt e => exact Primitive.close (st := .exprStmt e) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | assign p e => exact Primitive.close (st := .assign p e) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | declareObj τ x ov => exact Primitive.close (st := .declareObj τ x ov) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | declareRef τ x p => exact Primitive.close (st := .declareRef τ x p) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | seq s t =>
      have hfragST : CoreBigStepFragment s ∧ CoreBigStepFragment t := by
        simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
      rcases hfragST with ⟨hfragS, hfragT⟩
      let slotData := SeqSlots.select hentry
      exact
        Seq.close
          hentry
          slotData
          (fun hleftBoundary => IH (st := s) hfragS hleftBoundary)
          (fun _route htailContinuation =>
            IH (st := t) hfragT htailContinuation.toBodyClosureBoundaryCI)
  | ite c s t =>
      have hfragST : CoreBigStepFragment s ∧ CoreBigStepFragment t := by
        simpa [CoreBigStepFragment, InBigStepFragment] using hfrag
      rcases hfragST with ⟨hfragS, hfragT⟩
      exact
        Ite.close
          hentry
          (fun hthenBoundary => IH (st := s) hfragS hthenBoundary)
          (fun helseBoundary => IH (st := t) hfragT helseBoundary)
  | whileStmt c body =>
      exact while_case_driver_branch_of_coreSupport Wh W IH hfrag hentry
  | block ss => exact Block.close hentry
  | breakStmt => exact Primitive.close (st := .breakStmt) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | continueStmt => exact Primitive.close (st := .continueStmt) (by simp [PrimitiveCoreStmtConcrete]) hentry
  | returnStmt rv => exact Primitive.close (st := .returnStmt rv) (by simp [PrimitiveCoreStmtConcrete]) hentry

/-- `BodyReadyCI` wrapper for the data-backed seq mainline case-driver body. -/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqDataBlockPrimitiveIteSupport
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (Ite : FunctionBodyIteClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (SeqSlots : FunctionBodySeqSlotSelectionDataSupportCI)
    (Seq : SeqFunctionBodyClosureContinuationDataSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st := by
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqDataBlockPrimitiveIteSupport
      Primitive Ite P SeqSlots Seq Wh W Block IH hfrag hentry.toClosureBoundary

/-- Support package whose seq dependency is backed by explicit Type-level slot data. -/
structure FunctionBodyContinuationSeqDataBlockPrimitiveIteCaseDriverSupportCI : Type where
  primitiveSupport : FunctionBodyPrimitiveClosureSupportCI
  iteSupport : FunctionBodyIteClosureSupportCI
  P : StmtNormalPreservationCoreCI
  seqSlots : FunctionBodySeqSlotSelectionDataSupportCI
  seq : SeqFunctionBodyClosureContinuationDataSupportCI P
  whileSupport : WhileCurrentBoundaryClosureCoreSupportCI
  whileInvariant : FunctionBodyWhileBackedgeInvariantCoreProviderCI
  blockSupport : FunctionBodyBlockClosureSupportCI

namespace FunctionBodyContinuationSeqDataBlockPrimitiveIteCaseDriverSupportCI

/-- Run the data-backed seq mainline case-driver body. -/
theorem bodyClosure
    (S : FunctionBodyContinuationSeqDataBlockPrimitiveIteCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqDataBlockPrimitiveIteSupport
    S.primitiveSupport S.iteSupport S.P S.seqSlots S.seq
    S.whileSupport S.whileInvariant S.blockSupport IH hfrag hentry

/-- `BodyReadyCI` wrapper for the data-backed seq package. -/
theorem bodyReady
    (S : FunctionBodyContinuationSeqDataBlockPrimitiveIteCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  S.bodyClosure IH hfrag hentry.toClosureBoundary

end FunctionBodyContinuationSeqDataBlockPrimitiveIteCaseDriverSupportCI

/-- Build the data-backed seq mainline support package from components. -/
noncomputable def functionBodyContinuationSeqDataBlockPrimitiveIteCaseDriverSupportCI_of_components
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (Ite : FunctionBodyIteClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (SeqSlots : FunctionBodySeqSlotSelectionDataSupportCI)
    (Seq : SeqFunctionBodyClosureContinuationDataSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI) :
    FunctionBodyContinuationSeqDataBlockPrimitiveIteCaseDriverSupportCI :=
  { primitiveSupport := Primitive
    iteSupport := Ite
    P := P
    seqSlots := SeqSlots
    seq := Seq
    whileSupport := Wh
    whileInvariant := W
    blockSupport := Block }

end Cpp
