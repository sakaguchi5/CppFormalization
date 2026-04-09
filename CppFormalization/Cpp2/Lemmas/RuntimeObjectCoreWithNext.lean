import CppFormalization.Cpp2.Core.RuntimeObjectCore
import CppFormalization.Cpp2.Core.RuntimeState
import CppFormalization.Cpp2.Lemmas.RuntimeState

namespace Cpp
namespace RuntimeObjectCoreWithNext
/-!
Low-level extensional facts for the recomputed-cursor object update.
These are intentionally kept below Closure/Foundation so that decomposition
and transport arguments can use them without pulling in high-level invariants.
-/

@[simp] theorem lookupBinding_setNext (σ : State) (a : Nat) (x : Ident) :
    lookupBinding (setNext σ a) x = lookupBinding σ x := by
  unfold setNext
  rfl

@[simp] theorem next_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).next = aNext := by
  unfold declareObjectStateWithNext
  simp

@[simp] theorem lookupBinding_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    lookupBinding (declareObjectStateCore σ τ x ov) x = some (.object τ σ.next) := by
  unfold declareObjectStateCore
  simp

@[simp] theorem lookupBinding_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) x = some (.object τ σ.next) := by
  unfold declareObjectStateWithNext
  simp

@[simp] theorem lookupBinding_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value) (aNext : Nat)
    (hxy : y ≠ x) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) y = lookupBinding σ y := by
  unfold declareObjectStateWithNext declareObjectStateCore
  simp [ hxy, lookupBinding_setNext]

@[simp] theorem heap_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  unfold declareObjectStateCore
  simp

@[simp] theorem heap_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  unfold declareObjectStateWithNext
  simp [heap_declareObjectStateCore_self]

@[simp] theorem heap_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (aNext a : Nat) (ha : a ≠ σ.next) :
    (declareObjectStateWithNext σ τ x ov aNext).heap a = σ.heap a := by
  unfold declareObjectStateWithNext declareObjectStateCore
  simp [ ha]

@[simp] theorem scopes_declareObjectStateCore_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes = (declareObjectState σ τ x ov).scopes := by
  unfold declareObjectStateCore declareObjectState
  simp

@[simp] theorem heap_declareObjectStateCore_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap = (declareObjectState σ τ x ov).heap := by
  unfold declareObjectStateCore declareObjectState recordLocal bindTopBinding writeHeap
  split <;> simp

@[simp] theorem lookupBinding_declareObjectStateCore_eq_old
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value) :
    lookupBinding (declareObjectStateCore σ τ x ov) y =
      lookupBinding (declareObjectState σ τ x ov) y := by
  unfold lookupBinding
  simp [scopes_declareObjectStateCore_eq_old]

end RuntimeObjectCoreWithNext
end Cpp
