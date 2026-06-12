import CppFormalization.Cpp4.Core.Expand
import CppFormalization.Cpp4.Core.Program
import CppFormalization.Cpp4.Semantics.Kernel.Block

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Function

Finite kernel semantics for expanded internal function bodies.
-/

namespace Cpp4

/-- Function-body results after interpreting the body block's control channel. -/
inductive FunctionKernelResult where
  | fellThrough
  | returnedVoid
  | returnedValue : Value → FunctionKernelResult
  | escapedBreak
  | escapedContinue
  deriving DecidableEq, Repr

/-- Interpret a surface function body by expanding its block to a plan block and
running the ControlPlan kernel. -/
inductive BigStepFunctionBody (χ : KernelContext) :
    State → FunctionSig → StmtBlock → FunctionKernelResult → State → Prop where
  | normal {σ σ' : State} {sig : FunctionSig} {body : StmtBlock} :
      BigStepBlock χ σ (expandBlock body) .normal σ' →
      BigStepFunctionBody χ σ sig body .fellThrough σ'
  | returnVoid {σ σ' : State} {sig : FunctionSig} {body : StmtBlock} :
      BigStepBlock χ σ (expandBlock body) .returnVoid σ' →
      BigStepFunctionBody χ σ sig body .returnedVoid σ'
  | returnValue {σ σ' : State} {sig : FunctionSig} {body : StmtBlock} {v : Value} :
      BigStepBlock χ σ (expandBlock body) (.returnValue v) σ' →
      BigStepFunctionBody χ σ sig body (.returnedValue v) σ'
  | breakEscapes {σ σ' : State} {sig : FunctionSig} {body : StmtBlock} :
      BigStepBlock χ σ (expandBlock body) .breakResult σ' →
      BigStepFunctionBody χ σ sig body .escapedBreak σ'
  | continueEscapes {σ σ' : State} {sig : FunctionSig} {body : StmtBlock} :
      BigStepBlock χ σ (expandBlock body) .continueResult σ' →
      BigStepFunctionBody χ σ sig body .escapedContinue σ'

namespace BigStepFunctionBody

/-- Execute a known internal definition under the program-induced kernel context. -/
def InternalDefStep (P : Program) (σ : State) (d : InternalFunctionDef)
    (r : FunctionKernelResult) (σ' : State) : Prop :=
  BigStepFunctionBody (KernelContext.ofProgram P) σ d.sig d.body r σ'

end BigStepFunctionBody

end Cpp4
