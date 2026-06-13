import CppFormalization.Cpp4.Semantics.Effect.Expr
import CppFormalization.Cpp4.Semantics.Kernel.Call

/-!
# CppFormalization.Cpp4.Semantics.Effect.Call

Effect-carrying wrappers for finite call execution.
-/

namespace Cpp4

/-- A finite callable execution with an explicit resource-effect trace. -/
structure BigStepCallWithEffect
    (χ : KernelContext) (σ : State) (f : FunctionName) (args : CallArgs)
    (v : Value) (σ' : State) : Type where
  step : BigStepCall χ σ f args v σ'
  trace : EffectTrace σ σ'

namespace BigStepCallWithEffect

/-- Attach an already chosen resource-effect trace to a call step. -/
def attach {χ : KernelContext} {σ σ' : State} {f : FunctionName} {args : CallArgs}
    {v : Value} (step : BigStepCall χ σ f args v σ') (effect : ResourceEffect) :
    BigStepCallWithEffect χ σ f args v σ' where
  step := step
  trace := { effect := effect }

/-- Forget the resource-effect trace. -/
def forget {χ : KernelContext} {σ σ' : State} {f : FunctionName} {args : CallArgs}
    {v : Value} (h : BigStepCallWithEffect χ σ f args v σ') :
    BigStepCall χ σ f args v σ' :=
  h.step

/-- The effect-carrying view of an external call. -/
def ExternalStep
    (χ : KernelContext) (σ : State) (f : FunctionName) (args : CallArgs)
    (v : Value) (σ' : State) : Type :=
  Σ' _h : BigStepCallWithEffect χ σ f args v σ', BigStepCall.ExternalStep χ σ f args v σ'

/-- The effect-carrying view of an opaque internal call. -/
def InternalOpaqueStep
    (χ : KernelContext) (σ : State) (f : FunctionName) (args : CallArgs)
    (v : Value) (σ' : State) : Type :=
  Σ' _h : BigStepCallWithEffect χ σ f args v σ', BigStepCall.InternalOpaqueStep χ σ f args v σ'

end BigStepCallWithEffect

end Cpp4
