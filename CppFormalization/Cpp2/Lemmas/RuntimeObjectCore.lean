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
@[simp] theorem scopes_declareObjectStateWithNext_eq_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectStateCore σ τ x ov).scopes := by
  simp [declareObjectStateWithNext, setNext]
@[simp] theorem heap_declareObjectStateWithNext_eq_declareObjectStateCore
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectStateCore σ τ x ov).heap := by
  simp [declareObjectStateWithNext, setNext]

-- declareObjectState façade との比較 bridge。@[simp] にはしない。
theorem scopes_declareObjectStateWithNext_eq_declareObjectState
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes =
      (declareObjectState σ τ x ov).scopes := by
  rw [scopes_declareObjectStateWithNext_eq_declareObjectStateCore]
  exact scopes_declareObjectStateCore_eq_declareObjectState σ τ x ov

-- declareObjectState façade との比較 bridge。@[simp] にはしない。
theorem heap_declareObjectStateWithNext_eq_declareObjectState
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap =
      (declareObjectState σ τ x ov).heap := by
  rw [heap_declareObjectStateWithNext_eq_declareObjectStateCore]
  exact heap_declareObjectStateCore_eq_declareObjectState σ τ x ov


/-- Top-frame shape for `declareObjectStateWithNext` when the old scope stack is empty.
The allocated object address is `σ.next`; `aNext` is only the post-state cursor. -/
theorem declareObjectStateWithNext_scopes_zero_of_nil
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    (hsc : σ.scopes = []) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes[0]? = some
      { binds := fun z => if z = x then some (.object τ σ.next) else emptyScopeFrame.binds z,
        locals := [σ.next] } := by
  simp [declareObjectStateWithNext, setNext, declareObjectStateCore,
    recordLocal, writeHeap, bindTopBinding, hsc]
  rfl

/-- Top-frame shape for `declareObjectStateWithNext` when the old scope stack is nonempty.
The allocated object address is `σ.next`; `aNext` is only the post-state cursor. -/
theorem declareObjectStateWithNext_scopes_zero_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs) :
    (declareObjectStateWithNext σ τ x ov aNext).scopes[0]? = some
      { fr0 with
        binds := fun z => if z = x then some (.object τ σ.next) else fr0.binds z,
        locals := σ.next :: fr0.locals } := by
  simp [declareObjectStateWithNext, setNext, declareObjectStateCore,
    recordLocal, writeHeap, bindTopBinding, hsc]

/-- Deeper runtime scopes are unchanged by `declareObjectStateWithNext`. -/
theorem declareObjectStateWithNext_lookup_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {k : Nat} {fr : ScopeFrame} :
    (declareObjectStateWithNext σ τ x ov aNext).scopes[k.succ]? = some fr ↔
      σ.scopes[k.succ]? = some fr := by
  constructor
  · intro h
    cases hsc : σ.scopes with
    | nil =>
        simp [declareObjectStateWithNext, setNext, declareObjectStateCore,
          recordLocal, writeHeap, bindTopBinding, hsc] at h
    | cons fr0 frs =>
        simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
          recordLocal, writeHeap, bindTopBinding, hsc] using h
  · intro h
    cases hsc : σ.scopes with
    | nil =>
        simp [hsc] at h
    | cons fr0 frs =>
        simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
          recordLocal, writeHeap, bindTopBinding, hsc] using h

/-- Recover the concrete top frame of `declareObjectStateWithNext` in the nil case. -/
theorem declareObjectStateWithNext_lookup_zero_frame_of_nil
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame}
    (hsc : σ.scopes = [])
    (hk : (declareObjectStateWithNext σ τ x ov aNext).scopes[0]? = some fr) :
    fr = { binds := fun z => if z = x then some (.object τ σ.next) else emptyScopeFrame.binds z,
           locals := [σ.next] } := by
  have htop := declareObjectStateWithNext_scopes_zero_of_nil
    (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext) hsc
  rw [htop] at hk
  injection hk with hEq
  exact hEq.symm

/-- Recover the concrete top frame of `declareObjectStateWithNext` in the cons case. -/
theorem declareObjectStateWithNext_lookup_zero_frame_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    (hk : (declareObjectStateWithNext σ τ x ov aNext).scopes[0]? = some fr) :
    fr = { fr0 with
           binds := fun z => if z = x then some (.object τ σ.next) else fr0.binds z,
           locals := σ.next :: fr0.locals } := by
  have htop := declareObjectStateWithNext_scopes_zero_of_cons
    (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
    (fr0 := fr0) (frs := frs) hsc
  rw [htop] at hk
  injection hk with hEq
  exact hEq.symm

@[simp] theorem heap_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    (declareObjectStateWithNext σ τ x ov aNext).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  rw [heap_declareObjectStateWithNext_eq_declareObjectStateCore]
  exact heap_declareObjectStateCore_self σ τ x ov

@[simp] theorem heap_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (aNext a : Nat) (ha : a ≠ σ.next) :
    (declareObjectStateWithNext σ τ x ov aNext).heap a = σ.heap a := by
  rw [heap_declareObjectStateWithNext_eq_declareObjectStateCore]
  exact heap_declareObjectStateCore_other σ τ x ov ha

@[simp] theorem lookupBinding_declareObjectStateWithNext_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) (aNext : Nat) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) x = some (.object τ σ.next) := by
  rw [lookupBinding_eq_of_scopes_eq
    (scopes_declareObjectStateWithNext_eq_declareObjectStateCore σ τ x ov aNext) x]
  exact lookupBinding_declareObjectStateCore_self σ τ x ov

@[simp] theorem lookupBinding_declareObjectStateWithNext_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (aNext : Nat) (hxy : y ≠ x) :
    lookupBinding (declareObjectStateWithNext σ τ x ov aNext) y = lookupBinding σ y := by
  rw [lookupBinding_eq_of_scopes_eq
    (scopes_declareObjectStateWithNext_eq_declareObjectStateCore σ τ x ov aNext) y]
  exact lookupBinding_declareObjectStateCore_other σ τ x y ov hxy

end Cpp
