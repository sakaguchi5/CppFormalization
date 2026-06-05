import CppFormalization.Cpp2.Route.Closure.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureCI
import CppFormalization.Cpp2.Metatheory.Closure.FunctionBodyCaseSplitCI

namespace Cpp

/-!
# Closure.Internal.HeadTailReturnAwareCallbacksCI

Callback-shaped CI surfaces for the low-level return-aware head/tail assembly.
-/

/-- Callback-shaped CI route for block-body cons. -/
/-
C++ successor reading:
when the head exits normally, the normal successor reconstructs or closes
the tail target.
-/
/-
Successor vocabulary:
`normalSuccessor` is the control-successor callback for the route
where the head sub-execution exits normally.

It is not a legacy readiness transport; it is the C++ control-flow edge
from head-normal to the tail target.
-/
theorem block_cons_function_body_closure_boundary_ci_return_aware_from_callbacks
    {σ : State} {s : CppStmt} {ss : StmtBlock}
    (headClosure :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (normalSuccessor :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        FunctionBlockBodyClosureResult σ' ss) :
    FunctionBlockBodyClosureResult σ (.cons s ss) := by
  exact block_cons_function_body_result_return_aware
    headClosure normalSuccessor

end Cpp
