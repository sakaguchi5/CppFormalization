import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Core.RuntimeObjectCore

namespace Cpp

/-!
Runtime lemmas for the object-core update and externally supplied cursor.

Primitive state-operation algebra, including `setNext`, belongs in
`Lemmas.RuntimeState`.  This file contains only facts specific to
`declareObjectStateCore` and `declareObjectStateWithNext`.

The comparison lemmas against the old `declareObjectState` façade are kept here
temporarily so that downstream proofs can migrate before the façade name is
fully retired from theorem statements.
-/

/-! ## Object payload update -/

@[simp] theorem next_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).next = σ.next := by
  simp [declareObjectStateCore]

theorem scopes_declareObjectStateCore_eq_declareObjectState
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes = (declareObjectState σ τ x ov).scopes := by
  simp [declareObjectState, declareObjectStateWithNext, setNext]


theorem heap_declareObjectStateCore_eq_declareObjectState
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap =
      (declareObjectState σ τ x ov).heap := by
  simp only [declareObjectState, declareObjectStateWithNext, setNext]

@[simp] theorem heap_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  simp [declareObjectStateCore]

@[simp] theorem heap_declareObjectStateCore_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    {a : Nat} (ha : a ≠ σ.next) :
    (declareObjectStateCore σ τ x ov).heap a = σ.heap a := by
  simp [declareObjectStateCore, ha]


@[simp] theorem declareObjectStateCore_scopes_ne_nil
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes ≠ [] := by
  unfold declareObjectStateCore recordLocal writeHeap bindTopBinding
  cases σ.scopes <;> simp



@[simp] theorem declareObjectStateCore_top_local_mem
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    match (declareObjectStateCore σ τ x ov).scopes with
    | [] => False
    | fr :: _ => σ.next ∈ fr.locals := by
  unfold declareObjectStateCore recordLocal writeHeap bindTopBinding
  cases σ.scopes <;> simp

@[simp] theorem lookupBinding_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    lookupBinding (declareObjectStateCore σ τ x ov) x = some (.object τ σ.next) := by
  unfold declareObjectStateCore
  simp

@[simp] theorem lookupBinding_declareObjectStateCore_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (hxy : y ≠ x) :
    lookupBinding (declareObjectStateCore σ τ x ov) y = lookupBinding σ y := by
  unfold declareObjectStateCore
  simp [hxy]

/-! ## Object payload update with supplied post-state cursor -/

@[simp] theorem next_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).next = aNext := by
  simp [declareObjectStateWithNext, setNext]
/-
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
-/
--後で名前を変える
@[simp] theorem scopes_declareObjectStateWithNext_eq_core
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectStateCore σ τ x ov).scopes := by
  simp [declareObjectStateWithNext, setNext]
--後で名前を変える
@[simp] theorem heap_declareObjectStateWithNext_eq_core
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectStateCore σ τ x ov).heap := by
  simp [declareObjectStateWithNext, setNext]

--eq_oldからは@[simp]を外す、後で名前を変える
theorem scopes_declareObjectStateWithNext_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectState σ τ x ov).scopes := by
  rw [scopes_declareObjectStateWithNext_eq_core]
  exact scopes_declareObjectStateCore_eq_declareObjectState σ τ x ov

--eq_oldからは@[simp]を外す、後で名前を変える
theorem heap_declareObjectStateWithNext_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectState σ τ x ov).heap := by
  rw [heap_declareObjectStateWithNext_eq_core]
  exact heap_declareObjectStateCore_eq_declareObjectState σ τ x ov

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
  rw [lookupBinding_eq_of_scopes_eq
    (scopes_declareObjectStateWithNext_eq_core σ τ x ov aNext) x]
  exact lookupBinding_declareObjectStateCore_self σ τ x ov

@[simp] theorem lookupBinding_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (aNext : Nat) (hxy : y ≠ x) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) y = lookupBinding σ y := by
  rw [lookupBinding_eq_of_scopes_eq
    (scopes_declareObjectStateWithNext_eq_core σ τ x ov aNext) y]
  exact lookupBinding_declareObjectStateCore_other σ τ x y ov hxy

end Cpp
