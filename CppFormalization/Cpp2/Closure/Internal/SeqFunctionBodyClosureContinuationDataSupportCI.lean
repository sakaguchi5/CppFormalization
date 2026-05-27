import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverBoundaryCoreSupportCI
import CppFormalization.Cpp2.Closure.Internal.SeqBoundaryStaticDecompositionCI
import CppFormalization.Cpp2.Continuation.Boundary.Body

namespace Cpp

/-!
# Closure.Internal.SeqFunctionBodyClosureContinuationDataSupportCI

Data-backed seq continuation support.

This is the mainline seq support surface.  It consumes explicit Type-level
slot-selection data instead of reconstructing the left static boundary from the
old `seq_left_static_boundary_ci_of_entry` compatibility route.
-/

/-- Seq closure support with explicit Type-level slot-selection data.

The selected left static profile is obtained from
`SeqLeftSlotSelectionDataCI.staticBoundary`, not from
`seq_left_static_boundary_ci_of_entry`.
-/
structure SeqFunctionBodyClosureContinuationDataSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (slotData : SeqLeftSlotSelectionDataCI hentry) →
      (BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s) →
      (∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (SeqLeftSlotSelectionDataCI.staticBoundary slotData).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) →
      FunctionBodyClosureResult σ (.seq s t)

end Cpp
