import CppFormalization.Cpp2.Core.Types

/-!
Concrete scoped runtime state.
-/

namespace Cpp

structure Cell where
  ty    : CppType
  value : Option Value
  alive : Bool
  deriving Repr

inductive Binding where
  | object : CppType → Nat → Binding
  | ref    : CppType → Nat → Binding
  deriving DecidableEq, Repr

def bindingType : Binding → CppType
  | .object τ _ => τ
  | .ref τ _ => τ


def bindingAddr : Binding → Nat
  | .object _ a => a
  | .ref _ a => a

structure ScopeFrame where
  binds  : Ident → Option Binding
  locals : List Nat

structure State where
  scopes : List ScopeFrame
  heap   : Nat → Option Cell
  next   : Nat

instance : Repr State where
  reprPrec σ _ :=
    "State { scopes := " ++ repr σ.scopes.length ++ ", next := " ++ repr σ.next ++ " }"

def emptyScopeFrame : ScopeFrame := {
  binds := fun _ => none
  locals := []
}

def emptyState : State := {
  scopes := [emptyScopeFrame]
  heap := fun _ => none
  next := 0
}

instance : Inhabited State where
  default := emptyState

def lookupBindingFrames : List ScopeFrame → Ident → Option Binding
  | [], _ => none
  | fr :: frs, x =>
      match fr.binds x with
      | some b => some b
      | none => lookupBindingFrames frs x

def lookupBinding (σ : State) (x : Ident) : Option Binding :=
  lookupBindingFrames σ.scopes x

def currentScopeFresh (σ : State) (x : Ident) : Prop :=
  match σ.scopes with
  | [] => False
  | fr :: _ => fr.binds x = none

end Cpp
