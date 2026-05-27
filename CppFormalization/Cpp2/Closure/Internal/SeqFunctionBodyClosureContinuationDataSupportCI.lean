import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureResultCI
import CppFormalization.Cpp2.Continuation.Route.Seq
import CppFormalization.Cpp2.Closure.Internal.SeqBoundaryStaticDecompositionCI
import CppFormalization.Cpp2.Closure.Internal.SeqNormalPreservationCoreCI
import CppFormalization.Cpp2.Continuation.Boundary.Body

namespace Cpp

/-!
# Closure.Internal.SeqFunctionBodyClosureContinuationDataSupportCI

Data-backed seq continuation support.

This is the mainline seq support surface.
-/

/-- Seq closure support with explicit Type-level slot-selection data..
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
