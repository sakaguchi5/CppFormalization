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

def writeHeap (σ : State) (a : Nat) (c : Cell) : State :=
  { σ with
    heap := fun b => if b = a then some c else σ.heap b }

def killAddr (σ : State) (a : Nat) : State :=
  match σ.heap a with
  | none => σ
  | some c => writeHeap σ a { c with alive := false }

def killLocals : State → List Nat → State
  | σ, [] => σ
  | σ, a :: as => killLocals (killAddr σ a) as

def pushScope (σ : State) : State :=
  { σ with scopes := emptyScopeFrame :: σ.scopes }

def bindTopBinding (σ : State) (x : Ident) (b : Binding) : State :=
  match σ.scopes with
  | [] =>
      { σ with
        scopes := [{ binds := fun y => if y = x then some b else none, locals := [] }] }
  | fr :: frs =>
      { σ with
        scopes :=
          { fr with binds := fun y => if y = x then some b else fr.binds y } :: frs }

def recordLocal (σ : State) (a : Nat) : State :=
  match σ.scopes with
  | [] => σ
  | fr :: frs =>
      { σ with
        scopes := { fr with locals := a :: fr.locals } :: frs }

def declareObjectState (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) : State :=
  let a := σ.next
  let σ1 := bindTopBinding σ x (.object τ a)
  let σ2 : State := { σ1 with next := a + 1 }
  let σ3 := writeHeap σ2 a { ty := τ, value := ov, alive := true }
  recordLocal σ3 a

def declareRefState (σ : State) (τ : CppType) (x : Ident) (a : Nat) : State :=
  bindTopBinding σ x (.ref τ a)


def popScope? (σ : State) : Option State :=
  match σ.scopes with
  | [] => none
  | fr :: frs =>
      let σ0 : State := { σ with scopes := frs }
      some (killLocals σ0 fr.locals)

inductive CtrlResult where
  | normal
  | breakResult
  | continueResult
  | returnResult : Option Value → CtrlResult
  deriving DecidableEq, Repr

inductive ProgSuccess where
  | normal
  | returned : Option Value → ProgSuccess
  deriving DecidableEq, Repr

inductive ProgOutcome where
  | success  : ProgSuccess → State → ProgOutcome
  | diverges : ProgOutcome
  deriving Repr



end Cpp
