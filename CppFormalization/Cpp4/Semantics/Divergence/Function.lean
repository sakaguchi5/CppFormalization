import CppFormalization.Cpp4.Semantics.Divergence.Block
import CppFormalization.Cpp4.Semantics.Kernel.Function

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Function

Divergence vocabulary for surface function bodies via expanded blocks.
-/

namespace Cpp4

/-- A function body diverges when its expanded body block diverges. -/
def DivergesFunctionBody
    (χ : KernelContext) (σ : State) (_sig : FunctionSig) (body : StmtBlock) : Prop :=
  DivergesBlock χ σ (expandBlock body)

namespace DivergesFunctionBody

/-- Program-induced function-body divergence for a known internal definition. -/
def InternalDef (P : Program) (σ : State) (d : InternalFunctionDef) : Prop :=
  DivergesFunctionBody (KernelContext.ofProgram P) σ d.sig d.body

end DivergesFunctionBody

end Cpp4
