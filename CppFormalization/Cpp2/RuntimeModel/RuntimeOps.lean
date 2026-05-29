import CppFormalization.Cpp2.RuntimeModel.RuntimeState

/-!
Primitive runtime-state update operations.

This file contains operations that inspect or update the `State` record without
committing to C++ declaration semantics.  Declaration payload updates live in
`Core.RuntimeDeclUpdate`.
-/

namespace Cpp

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

/-- Replace only the runtime cursor. -/
def setNext (σ : State) (a : Nat) : State :=
  { σ with next := a }

def popScope? (σ : State) : Option State :=
  match σ.scopes with
  | [] => none
  | fr :: frs =>
      let σ0 : State := { σ with scopes := frs }
      some (killLocals σ0 fr.locals)

end Cpp
