import CppFormalization.Cpp4.Semantics.Classification.Block
import CppFormalization.Cpp4.Semantics.Divergence.Function
import CppFormalization.Cpp4.Semantics.Kernel.Function

/-!
# CppFormalization.Cpp4.Semantics.Classification.Function

Function-body finite/divergent classification.
-/

namespace Cpp4

/-- Classification of a surface function body under the kernel context. -/
inductive FunctionBodyClassification
    (χ : KernelContext) (σ : State) (sig : FunctionSig) (body : StmtBlock) : Type where
  | finite {r : FunctionKernelResult} {σ' : State}
      (step : BigStepFunctionBody χ σ sig body r σ') :
      FunctionBodyClassification χ σ sig body
  | diverges (diverges : DivergesFunctionBody χ σ sig body) :
      FunctionBodyClassification χ σ sig body

namespace FunctionBodyClassification

/-- Program-induced classification for a known internal function definition. -/
def InternalDefClassification (P : Program) (σ : State) (d : InternalFunctionDef) : Type :=
  FunctionBodyClassification (KernelContext.ofProgram P) σ d.sig d.body

end FunctionBodyClassification

end Cpp4
