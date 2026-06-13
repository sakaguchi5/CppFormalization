import CppFormalization.Cpp4.Semantics.Effect.Block
import CppFormalization.Cpp4.Semantics.Kernel.Function

/-!
# CppFormalization.Cpp4.Semantics.Effect.Function

Effect-carrying wrappers for finite function-body kernel execution.
-/

namespace Cpp4

structure BigStepFunctionBodyWithEffect
    (χ : KernelContext) (σ : State) (sig : FunctionSig) (body : StmtBlock)
    (r : FunctionKernelResult) (σ' : State) : Type where
  step : BigStepFunctionBody χ σ sig body r σ'
  trace : EffectTrace σ σ'

namespace BigStepFunctionBodyWithEffect

/-- Attach an already chosen resource-effect trace to a function-body step. -/
def attach {χ : KernelContext} {σ σ' : State} {sig : FunctionSig} {body : StmtBlock}
    {r : FunctionKernelResult} (step : BigStepFunctionBody χ σ sig body r σ')
    (effect : ResourceEffect) : BigStepFunctionBodyWithEffect χ σ sig body r σ' where
  step := step
  trace := { effect := effect }

/-- Forget the resource-effect trace. -/
def forget {χ : KernelContext} {σ σ' : State} {sig : FunctionSig} {body : StmtBlock}
    {r : FunctionKernelResult} (h : BigStepFunctionBodyWithEffect χ σ sig body r σ') :
    BigStepFunctionBody χ σ sig body r σ' :=
  h.step

end BigStepFunctionBodyWithEffect

end Cpp4
