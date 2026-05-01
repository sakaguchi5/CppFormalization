import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcreteCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI

namespace Cpp

/-!
# Closure.Internal.HeadTailReturnAwareCallbacksCI

Callback-shaped CI surfaces for the low-level return-aware head/tail assembly.
-/

/-- Callback-shaped CI route for statement sequencing. -/
theorem seq_function_body_closure_boundary_ci_return_aware_from_callbacks
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (headClosure :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (tailAfterHeadNormal :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨
          BigStepStmtDiv σ' t) :
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨
      BigStepStmtDiv σ (.seq s t) := by
  exact seq_function_body_result_return_aware headClosure tailAfterHeadNormal

/-- Callback-shaped CI route for block-body cons. -/
theorem block_cons_function_body_closure_boundary_ci_return_aware_from_callbacks
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (_hentry : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (headClosure :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (tailAfterHeadNormal :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        FunctionBlockBodyClosureResult σ' ss) :
    FunctionBlockBodyClosureResult σ (.cons s ss) := by
  exact block_cons_function_body_result_return_aware
    headClosure tailAfterHeadNormal

end Cpp
