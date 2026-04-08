import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Core.RuntimeObjectCore

namespace Cpp

/-!
Runtime lemmas for the object-core update and externally supplied cursor.

These belong in `Lemmas`, not in `Closure/Foundation`, because they are
plain state-update algebra and do not depend on closure-specific invariants.
-/

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

@[simp] theorem scopes_declareObjectStateWithNext_eq_core
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectStateCore σ τ x ov).scopes := by
  rfl

@[simp] theorem heap_declareObjectStateWithNext_eq_core
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectStateCore σ τ x ov).heap := by
  rfl

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
      simpa using lookupBinding_declareObjectState_other σ τ x y ov hxy

end Cpp
