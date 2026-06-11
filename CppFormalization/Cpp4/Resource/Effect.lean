import CppFormalization.Cpp4.Resource.Demand

/-!
# CppFormalization.Cpp4.Resource.Effect

Resource effects produced by expression/statement/block/call execution.
-/

namespace Cpp4

/-- Atomic resource effects. -/
inductive ResourceEffectAtom where
  | allocObject : ObjectId → ScopeId → CppType → ResourceEffectAtom
  | writeObject : Address → CppType → ResourceEffectAtom
  | endLifetime : ObjectId → ResourceEffectAtom
  | pushScope : ScopeId → ResourceEffectAtom
  | popScope : ScopeId → ResourceEffectAtom
  | bindName : ScopeId → Ident → Binding → ResourceEffectAtom
  | callInternal : FunctionName → ResourceEffectAtom
  | callExternal : FunctionName → ResourceEffectAtom
  | control : CtrlResult → ResourceEffectAtom
  deriving Repr

/-- A resource effect trace. -/
abbrev ResourceEffect := List ResourceEffectAtom

/-- An execution trace with explicit resource effect. -/
structure EffectTrace (σ σ' : State) where
  effect : ResourceEffect

end Cpp4
