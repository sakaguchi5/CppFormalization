import CppFormalization.Cpp2.Core.RuntimeOps

/-!
Primitive declaration-state updates.

Object declaration is split into a payload update at the pre-state cursor and an
explicit post-state cursor update.  This keeps allocator/cursor policy separate
from the binding/heap/local-membership payload.
-/

namespace Cpp

/--
Object-declaration payload update, without committing to a post-state cursor.

The newly declared object lives at the pre-state cursor `σ.next`; this update
only records the binding, heap cell, and top-frame ownership/local membership.
The `next` cursor is intentionally unchanged.
-/
def declareObjectStateCore (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) : State :=
  let a := σ.next
  let σ1 := bindTopBinding σ x (.object τ a)
  let σ2 := writeHeap σ1 a { ty := τ, value := ov, alive := true }
  recordLocal σ2 a

/--
Object declaration with an externally supplied post-state cursor.

This keeps allocator/cursor policy separate from the declaration payload.
-/
def declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) : State :=
  setNext (declareObjectStateCore σ τ x ov) aNext

/--
Legacy façade for the successor-cursor policy.

The canonical definition is now the split standard form with the concrete policy
`aNext = σ.next + 1`.
-/
def declareObjectState (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) : State :=
  declareObjectStateWithNext σ τ x ov (σ.next + 1)

def declareRefState (σ : State) (τ : CppType) (x : Ident) (a : Nat) : State :=
  bindTopBinding σ x (.ref τ a)

end Cpp
