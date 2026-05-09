import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Core.RuntimeObjectCore

namespace Cpp

/-!
Runtime lemmas for the object-core update and externally supplied cursor.

Primitive state-operation algebra belongs in `Lemmas.RuntimeState`.
This file contains only facts specific to `setNext`, `declareObjectStateCore`,
and `declareObjectStateWithNext`.

The comparison lemmas against the old `declareObjectState` façade are kept here
temporarily so that downstream proofs can migrate before the façade definition is
changed to the split standard form.
-/

/-! ## Cursor replacement -/

@[simp] theorem next_setNext (σ : State) (a : Nat) :
    (setNext σ a).next = a := by
  rfl

@[simp] theorem scopes_setNext (σ : State) (a : Nat) :
    (setNext σ a).scopes = σ.scopes := by
  rfl

@[simp] theorem heap_setNext (σ : State) (a : Nat) :
    (setNext σ a).heap = σ.heap := by
  rfl

@[simp] theorem lookupBinding_setNext_of_setNext (σ : State) (a : Nat) (x : Ident) :
    lookupBinding (setNext σ a) x = lookupBinding σ x := by
  rfl

/-! ## Object payload update -/

@[simp] theorem next_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).next = σ.next := by
  simp [declareObjectStateCore]

@[simp] theorem scopes_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes = (declareObjectState σ τ x ov).scopes := by
  unfold declareObjectStateCore declareObjectState
  simp [scopes_recordLocal, scopes_writeHeap, scopes_bindTopBinding]

@[simp] theorem heap_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap = (declareObjectState σ τ x ov).heap := by
  unfold declareObjectStateCore declareObjectState
  simp [writeHeap, bindTopBinding]

@[simp] theorem declareObjectStateCore_scopes_ne_nil
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes ≠ [] := by
  rw [scopes_declareObjectStateCore]
  exact declareObjectState_scopes_ne_nil σ τ x ov

@[simp] theorem heap_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  rw [heap_declareObjectStateCore]
  exact declareObjectState_heap_self σ τ x ov

@[simp] theorem heap_declareObjectStateCore_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    {a : Nat} (ha : a ≠ σ.next) :
    (declareObjectStateCore σ τ x ov).heap a = σ.heap a := by
  rw [heap_declareObjectStateCore]
  exact declareObjectState_heap_other σ τ x ov ha

@[simp] theorem declareObjectStateCore_top_local_mem
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    match (declareObjectStateCore σ τ x ov).scopes with
    | [] => False
    | fr :: _ => σ.next ∈ fr.locals := by
  rw [scopes_declareObjectStateCore]
  exact declareObjectState_top_local_mem σ τ x ov

@[simp] theorem lookupBinding_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    lookupBinding (declareObjectStateCore σ τ x ov) x = some (.object τ σ.next) := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateCore σ τ x ov)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateCore σ τ x ov)
      (x := x)
  calc
    lookupBinding (declareObjectStateCore σ τ x ov) x
        = lookupBinding (declareObjectState σ τ x ov) x := hEq
    _ = some (.object τ σ.next) := by simp

@[simp] theorem lookupBinding_declareObjectStateCore_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (hxy : y ≠ x) :
    lookupBinding (declareObjectStateCore σ τ x ov) y = lookupBinding σ y := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateCore σ τ x ov)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateCore σ τ x ov)
      (x := y)
  calc
    lookupBinding (declareObjectStateCore σ τ x ov) y
        = lookupBinding (declareObjectState σ τ x ov) y := hEq
    _ = lookupBinding σ y := by
          simpa using lookupBinding_declareObjectState_other σ τ x y ov hxy

/-! ## Object payload update with supplied post-state cursor -/

@[simp] theorem next_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).next = aNext := by
  simp [declareObjectStateWithNext, setNext]

@[simp] theorem scopes_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectStateCore σ τ x ov).scopes := by
  simp [declareObjectStateWithNext, setNext]

@[simp] theorem heap_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectStateCore σ τ x ov).heap := by
  simp [declareObjectStateWithNext, setNext]

@[simp] theorem scopes_declareObjectStateWithNext_eq_core
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectStateCore σ τ x ov).scopes := by
  exact scopes_declareObjectStateWithNext σ τ x ov aNext

@[simp] theorem heap_declareObjectStateWithNext_eq_core
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectStateCore σ τ x ov).heap := by
  exact heap_declareObjectStateWithNext σ τ x ov aNext

@[simp] theorem scopes_declareObjectStateWithNext_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectState σ τ x ov).scopes := by
  rw [scopes_declareObjectStateWithNext_eq_core]
  exact scopes_declareObjectStateCore σ τ x ov

@[simp] theorem heap_declareObjectStateWithNext_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectState σ τ x ov).heap := by
  rw [heap_declareObjectStateWithNext_eq_core]
  exact heap_declareObjectStateCore σ τ x ov

@[simp] theorem heap_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  rw [heap_declareObjectStateWithNext_eq_core]
  exact heap_declareObjectStateCore_self σ τ x ov

@[simp] theorem heap_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (aNext a : Nat) (ha : a ≠ σ.next) :
    (declareObjectStateWithNext σ τ x ov aNext).heap a = σ.heap a := by
  rw [heap_declareObjectStateWithNext_eq_core]
  exact heap_declareObjectStateCore_other σ τ x ov ha

@[simp] theorem lookupBinding_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) x = some (.object τ σ.next) := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateWithNext σ τ x ov aNext)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateWithNext_eq_old σ τ x ov aNext)
      (x := x)
  calc
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) x
        = lookupBinding (declareObjectState σ τ x ov) x := hEq
    _ = some (.object τ σ.next) := by simp

@[simp] theorem lookupBinding_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (aNext : Nat) (hxy : y ≠ x) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) y = lookupBinding σ y := by
  have hEq := lookupBinding_eq_of_scopes_eq
      (σ₁ := declareObjectStateWithNext σ τ x ov aNext)
      (σ₂ := declareObjectState σ τ x ov)
      (h := scopes_declareObjectStateWithNext_eq_old σ τ x ov aNext)
      (x := y)
  calc
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) y
        = lookupBinding (declareObjectState σ τ x ov) y := hEq
    _ = lookupBinding σ y := by
      simpa using
        lookupBinding_declareObjectState_other
          (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) hxy

end Cpp
