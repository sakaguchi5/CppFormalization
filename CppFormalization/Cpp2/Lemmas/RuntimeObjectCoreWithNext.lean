import CppFormalization.Cpp2.Lemmas.RuntimeObjectCore

namespace Cpp
namespace RuntimeObjectCoreWithNext

/-!
Compatibility surface for the old `RuntimeObjectCoreWithNext` namespace.

The actual object-core/update lemmas now live in `Lemmas.RuntimeObjectCore`.
This file keeps the old names available without duplicating proof content.
-/

@[simp] theorem lookupBinding_setNext (σ : State) (a : Nat) (x : Ident) :
    lookupBinding (setNext σ a) x = lookupBinding σ x := by
  exact Cpp.lookupBinding_setNext_of_setNext σ a x

@[simp] theorem next_declareObjectStateWithNext
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).next = aNext := by
  exact Cpp.next_declareObjectStateWithNext σ τ x ov aNext

@[simp] theorem lookupBinding_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    lookupBinding (declareObjectStateCore σ τ x ov) x = some (.object τ σ.next) := by
  exact Cpp.lookupBinding_declareObjectStateCore_self σ τ x ov

@[simp] theorem lookupBinding_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) x = some (.object τ σ.next) := by
  exact Cpp.lookupBinding_declareObjectStateWithNext_self σ τ x ov aNext

@[simp] theorem lookupBinding_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value) (aNext : Nat)
    (hxy : y ≠ x) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) y = lookupBinding σ y := by
  exact Cpp.lookupBinding_declareObjectStateWithNext_other σ τ x y ov aNext hxy

@[simp] theorem heap_declareObjectStateCore_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  exact Cpp.heap_declareObjectStateCore_self σ τ x ov

@[simp] theorem heap_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  exact Cpp.heap_declareObjectStateWithNext_self σ τ x ov aNext

@[simp] theorem heap_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (aNext a : Nat) (ha : a ≠ σ.next) :
    (declareObjectStateWithNext σ τ x ov aNext).heap a = σ.heap a := by
  exact Cpp.heap_declareObjectStateWithNext_other σ τ x ov aNext a ha

@[simp] theorem scopes_declareObjectStateCore_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).scopes = (declareObjectState σ τ x ov).scopes := by
  exact Cpp.scopes_declareObjectStateCore σ τ x ov

@[simp] theorem heap_declareObjectStateCore_eq_old
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectStateCore σ τ x ov).heap = (declareObjectState σ τ x ov).heap := by
  exact Cpp.heap_declareObjectStateCore σ τ x ov

@[simp] theorem lookupBinding_declareObjectStateCore_eq_old
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value) :
    lookupBinding (declareObjectStateCore σ τ x ov) y =
      lookupBinding (declareObjectState σ τ x ov) y := by
  exact lookupBinding_eq_of_scopes_eq (Cpp.scopes_declareObjectStateCore σ τ x ov) y

end RuntimeObjectCoreWithNext
end Cpp
