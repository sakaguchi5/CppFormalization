import CppFormalization.Cpp4.Semantics.Effect.Call
import CppFormalization.Cpp4.Semantics.Kernel.Atom

/-!
# CppFormalization.Cpp4.Semantics.Effect.Atom

Effect-carrying wrappers for primitive finite kernel steps.
-/

namespace Cpp4

structure BigStepInitWithEffect
    (χ : KernelContext) (σ : State) (init : CppInit) (ov : Option Value) (σ' : State) : Type where
  step : BigStepInit χ σ init ov σ'
  trace : EffectTrace σ σ'

structure BigStepDeclWithEffect
    (χ : KernelContext) (σ : State) (d : CppDecl) (σ' : State) : Type where
  step : BigStepDecl χ σ d σ'
  trace : EffectTrace σ σ'

structure BigStepExprStmtWithEffect
    (χ : KernelContext) (σ : State) (s : CppExprStmt) (σ' : State) : Type where
  step : BigStepExprStmt χ σ s σ'
  trace : EffectTrace σ σ'

structure BigStepAssignWithEffect
    (χ : KernelContext) (σ : State) (a : CppAssign) (σ' : State) : Type where
  step : BigStepAssign χ σ a σ'
  trace : EffectTrace σ σ'

structure BigStepForInitWithEffect
    (χ : KernelContext) (σ : State) (init : CppForInit) (σ' : State) : Type where
  step : BigStepForInit χ σ init σ'
  trace : EffectTrace σ σ'

structure BigStepForIterWithEffect
    (χ : KernelContext) (σ : State) (iter : CppForIter) (σ' : State) : Type where
  step : BigStepForIter χ σ iter σ'
  trace : EffectTrace σ σ'

/-- A finite primitive atom step with an explicit resource-effect trace. -/
structure BigStepAtomWithEffect
    (χ : KernelContext) (σ : State) (a : ControlAtom) (r : CtrlResult) (σ' : State) : Type where
  step : BigStepAtom χ σ a r σ'
  trace : EffectTrace σ σ'

namespace BigStepAtomWithEffect

/-- Attach an already chosen resource-effect trace to an atom step. -/
def attach {χ : KernelContext} {σ σ' : State} {a : ControlAtom} {r : CtrlResult}
    (step : BigStepAtom χ σ a r σ') (effect : ResourceEffect) :
    BigStepAtomWithEffect χ σ a r σ' where
  step := step
  trace := { effect := effect }

/-- Forget the resource-effect trace. -/
def forget {χ : KernelContext} {σ σ' : State} {a : ControlAtom} {r : CtrlResult}
    (h : BigStepAtomWithEffect χ σ a r σ') : BigStepAtom χ σ a r σ' :=
  h.step

end BigStepAtomWithEffect

end Cpp4
