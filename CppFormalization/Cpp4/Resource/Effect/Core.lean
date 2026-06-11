import CppFormalization.Cpp4.Resource.Demand.All

/-!
# CppFormalization.Cpp4.Resource.Effect.Core

Atomic resource effects plus small concrete state transformers used by the first
noninterference theorems.
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

/-- Mark a cell's lifetime as ended. -/
def endLifetimeCell (c : Cell) : Cell :=
  { c with lifetime := { c.lifetime with status := .ended } }

/-- Runtime state after writing a value to an already-allocated object address. -/
def writeObjectState (σ : State) (a : Address) (τ : CppType) (v : Value) : State :=
  { σ with
    heap := fun oid =>
      if oid = a.object then
        match σ.heap oid with
        | none => none
        | some c => some { c with ty := τ, value := some v }
      else
        σ.heap oid }

/-- Runtime state after ending one object's lifetime. -/
def endLifetimeState (σ : State) (oid : ObjectId) : State :=
  { σ with
    heap := fun q =>
      if q = oid then
        match σ.heap q with
        | none => none
        | some c => some (endLifetimeCell c)
      else
        σ.heap q }

/-- Runtime state after opening an empty scope frame. -/
def pushScopeState (σ : State) (sid : ScopeId) : State :=
  { σ with scopes := emptyScopeFrame sid :: σ.scopes }

/-- Runtime state after closing a scope id.

The first resource model closes every object whose lifetime owner is the closed
scope id.  Later RAII/destructor semantics can refine this transformer while
preserving the same noninterference surface.
-/
def popScopeState (σ : State) (sid : ScopeId) : State :=
  { σ with
    scopes := σ.scopes.filter (fun fr => if fr.id = sid then false else true)
    heap := fun oid =>
      match σ.heap oid with
      | none => none
      | some c =>
          if c.lifetime.owner = sid then
            some (endLifetimeCell c)
          else
            some c }

/-- Runtime state after binding a name in the current top frame. -/
def bindNameState (σ : State) (x : Ident) (b : Binding) : State :=
  match σ.scopes with
  | [] => σ
  | fr :: rest =>
      { σ with scopes := { fr with binds := fun y => if y = x then some b else fr.binds y } :: rest }

end Cpp4
