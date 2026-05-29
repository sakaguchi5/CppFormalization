import CppFormalization.Cpp2.Entry.Body.BodyReadyCI
import CppFormalization.Cpp2.Static.Facts.Control.BodyReadyControlExclusionCI
import CppFormalization.Cpp2.Legacy.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Audit.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Metatheory.Closure.CurrentShellCI
import CppFormalization.Cpp2.Metatheory.Closure.FunctionBodyCaseDriverContinuationIHCI
import CppFormalization.Cpp2.Stability.Closure.FunctionBodyReplayStablePrimitiveWhileFacts
import CppFormalization.Cpp2.Closure.Function.FunctionBody

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureCI

CI-centric function-body closure layer.

目的:
- old `BodyReady` を主線から降格し、internal closure の driver を `BodyReadyCI` に移す。
- 既存 concrete kernel (`StmtControlPreservation`, `ReadinessBoundaryConcrete`,
  `InternalClosureRoadmapConcrete`) はそのまま利用する。
- replay-stable primitive `while` special case は
  `FunctionBodyReplayStablePrimitiveWhileFacts.lean` に分離した。
- live な shell は canonical `BodyClosureBoundaryCI` surface の
  global recursion principle だけに縮めた。
  `BodyReadyCI` entry theorem は forgetful map `toClosureBoundary` から導く。
-/

/-
Current live shell was shrunk to a global recursion principle in `CurrentShellCI.lean`.
-/

/-- canonical entry theorem for function-body closure. -/
theorem body_closure_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hentry
  exact body_closure_ci_function_body_global_recursion hfrag hentry

/--
`BodyReadyCI` entry theorem is no longer a separate shell.
It is derived from the canonical closure-boundary theorem via `toClosureBoundary`.
-/
theorem body_ready_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  exact body_closure_ci_function_body_progress_or_diverges hfrag hready.toClosureBoundary
/-!
## Mainline continuation root

The old public wrappers above are still kept as compatibility roots.  The
preferred root for new auditing is the continuation-boundary route below.

Design reading:
- the recursive hypothesis speaks in terms of `StmtContinuationBoundaryCI`;
- the `seq` dependency is continuation-tail support;
- primitive closure, `ite` closure, normal preservation, seq slot data,
  data-backed seq continuation support, while support, while invariant,
  block support, and recursion are explicit inputs;
- this avoids treating old `BodyClosureBoundaryCI` tail reconstruction as the
  mainline root.
-/

/-- Mainline function-body closure root through the continuation-boundary case
driver.

This is intentionally parameterized by primitive support, `ite` support, the normal-preservation core,
seq slot data support, data-backed continuation seq support, while support,
while backedge invariant provider, explicit block support, and continuation-boundary IH.  That makes the remaining assumptions visible to
`#print axioms` instead of hiding them behind the old global root. -/
theorem body_closure_ci_function_body_progress_or_diverges_mainline_continuation
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (Ite : FunctionBodyIteClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (SeqSlots : FunctionBodySeqSlotSelectionDataSupportCI)
    (Seq : SeqFunctionBodyClosureContinuationDataSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hentry
  exact
    body_closure_ci_function_body_progress_or_diverges_case_driver_body_continuationSeqDataBlockPrimitiveIteSupport
      Primitive
      Ite
      P
      SeqSlots
      Seq
      Wh
      W
      Block
      IH.toBoundaryIH
      hfrag
      hentry

/-- `BodyReadyCI` wrapper for the mainline continuation root. -/
theorem body_ready_ci_function_body_progress_or_diverges_mainline_continuation
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (Ite : FunctionBodyIteClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (SeqSlots : FunctionBodySeqSlotSelectionDataSupportCI)
    (Seq : SeqFunctionBodyClosureContinuationDataSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  exact
    body_closure_ci_function_body_progress_or_diverges_mainline_continuation
      Primitive
      Ite
      P
      SeqSlots
      Seq
      Wh
      W
      Block
      IH
      hfrag
      hready.toClosureBoundary


end Cpp
