import CppFormalization.Cpp2.Core.RuntimeState

namespace Cpp

/-!
Low-level object-update core, independent of Closure/Foundation.

This separates:
- object payload update (`declareObjectStateCore`)
- cursor replacement (`setNext` / `declareObjectStateWithNext`)

so that allocator/cursor policy can move out of Closure.Foundation.
-/

/-- Replace only the cursor field. -/
def setNext (σ : State) (a : Nat) : State :=
  { σ with next := a }

/--
`declareObjectState` without post-state cursor policy.

The newly declared object still lives at the pre-state cursor `σ.next`.
What changes here are only:
- top binding
- heap cell at `σ.next`
- top-frame ownership/local recording

The next cursor is intentionally left unchanged.
-/
def declareObjectStateCore (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) : State :=
  let a := σ.next
  let σ1 := bindTopBinding σ x (.object τ a)
  let σ2 := writeHeap σ1 a { ty := τ, value := ov, alive := true }
  recordLocal σ2 a

/--
Object declaration with externally supplied post-state cursor.

This is still deterministic as a function once the chosen cursor is given,
but it no longer hardcodes `next := σ.next + 1`.
-/
def declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) : State :=
  setNext (declareObjectStateCore σ τ x ov) aNext

@[simp] theorem next_setNext (σ : State) (a : Nat) :
    (setNext σ a).next = a := by
  rfl

@[simp] theorem scopes_setNext (σ : State) (a : Nat) :
    (setNext σ a).scopes = σ.scopes := by
  rfl

@[simp] theorem heap_setNext (σ : State) (a : Nat) :
    (setNext σ a).heap = σ.heap := by
  rfl


@[simp] theorem next_bindTopBinding (σ : State) (x : Ident) (b : Binding) :
    (bindTopBinding σ x b).next = σ.next := by
  unfold bindTopBinding
  split <;> rfl

@[simp] theorem next_writeHeap (σ : State) (a : Nat) (c : Cell) :
    (writeHeap σ a c).next = σ.next := by
  rfl

@[simp] theorem next_recordLocal (σ : State) (a : Nat) :
    (recordLocal σ a).next = σ.next := by
  unfold recordLocal
  cases σ.scopes <;> rfl

@[simp] theorem next_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).next = σ.next := by
  simp [declareObjectStateCore]

@[simp] theorem next_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).next = aNext := by
  simp [declareObjectStateWithNext]

@[simp] theorem scopes_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectStateCore σ τ x ov).scopes := by
  rfl

@[simp] theorem heap_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectStateCore σ τ x ov).heap := by
  rfl

end Cpp
