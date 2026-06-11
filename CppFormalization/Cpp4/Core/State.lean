import CppFormalization.Cpp4.Core.Lifetime

/-!
# CppFormalization.Cpp4.Core.State

Concrete runtime state backed by the resource-oriented Core vocabulary.
-/

namespace Cpp4

/-- Runtime storage cell. -/
structure Cell where
  ty : CppType
  value : Option Value
  lifetime : LifetimeInfo
  deriving Repr

/-- Runtime state.

`nextObject` and `nextScope` are allocation cursors.  They are policies, not
semantic proof objects; freshness/ownership facts are stated in Resource layers.
-/
structure State where
  scopes : List ScopeFrame
  heap : ObjectId → Option Cell
  nextObject : Nat
  nextScope : Nat

instance : Inhabited State where
  default := {
    scopes := [emptyScopeFrame { id := 0 }]
    heap := fun _ => none
    nextObject := 0
    nextScope := 1
  }

/-- Lookup through active runtime frames, from innermost to outermost. -/
def lookupBindingFrames : List ScopeFrame → Ident → Option Binding
  | [], _ => none
  | fr :: frs, x =>
      match fr.binds x with
      | some b => some b
      | none => lookupBindingFrames frs x

def lookupBinding (σ : State) (x : Ident) : Option Binding :=
  lookupBindingFrames σ.scopes x

/-- The current top scope, if any. -/
def topScope? (σ : State) : Option ScopeFrame :=
  σ.scopes.head?

/-- A scope id is active when a frame with that id appears in the scope stack. -/
def ActiveScope (σ : State) (sid : ScopeId) : Prop :=
  ∃ fr, fr ∈ σ.scopes ∧ fr.id = sid

/-- A scope id is the current top scope. -/
def TopScope (σ : State) (sid : ScopeId) : Prop :=
  ∃ fr rest, σ.scopes = fr :: rest ∧ fr.id = sid

/-- Heap lookup by address. -/
def heapAt (σ : State) (a : Address) : Option Cell :=
  σ.heap a.object

end Cpp4
