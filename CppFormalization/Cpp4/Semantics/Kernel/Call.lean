import CppFormalization.Cpp4.Semantics.Kernel.Expr

/-!
# CppFormalization.Cpp4.Semantics.Kernel.Call

Convenience vocabulary around finite kernel call execution.
-/

namespace Cpp4

namespace BigStepCall

/-- The callable declaration used by a call execution, if one wants to expose it as
an existential package. -/
def DeclUsed (χ : KernelContext) (f : FunctionName) (decl : CallableDecl) : Prop :=
  χ.functions.lookup f = some decl

/-- External-call executions are exactly the call steps whose resolved declaration
is external. -/
def ExternalStep
    (χ : KernelContext) (σ : State) (f : FunctionName) (args : CallArgs)
    (v : Value) (σ' : State) : Prop :=
  ∃ decl values σargs,
    χ.functions.lookup f = some decl ∧
    decl.kind = .external ∧
    BigStepCallArgs χ σ args values σargs ∧
    ValueCompat v decl.sig.ret ∧
    BigStepCall χ σ f args v σ'

/-- Internal-call executions are kept opaque at the kernel-call level; function-body
semantics later connects this hook to `Program.lookupInternal`. -/
def InternalOpaqueStep
    (χ : KernelContext) (σ : State) (f : FunctionName) (args : CallArgs)
    (v : Value) (σ' : State) : Prop :=
  ∃ decl values σargs,
    χ.functions.lookup f = some decl ∧
    decl.kind = .internal ∧
    BigStepCallArgs χ σ args values σargs ∧
    ValueCompat v decl.sig.ret ∧
    BigStepCall χ σ f args v σ'

end BigStepCall

end Cpp4
