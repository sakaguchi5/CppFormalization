import CppFormalization.Cpp4.Semantics.Surface.Block
import CppFormalization.Cpp4.Semantics.Kernel.Function

/-!
# CppFormalization.Cpp4.Semantics.Surface.Function

Surface-facing function-body semantics.
-/

namespace Cpp4

namespace SurfaceSemantics

/-- Function bodies are already surface blocks; the kernel function-body relation
interprets them by expansion. -/
def BigStepSurfaceFunctionBody
    (χ : KernelContext) (σ : State) (sig : FunctionSig) (body : StmtBlock)
    (r : FunctionKernelResult) (σ' : State) : Prop :=
  BigStepFunctionBody χ σ sig body r σ'

/-- Program-induced function-body execution for a known internal definition. -/
def BigStepInternalDef
    (P : Program) (σ : State) (d : InternalFunctionDef)
    (r : FunctionKernelResult) (σ' : State) : Prop :=
  BigStepFunctionBody.InternalDefStep P σ d r σ'

end SurfaceSemantics

end Cpp4
