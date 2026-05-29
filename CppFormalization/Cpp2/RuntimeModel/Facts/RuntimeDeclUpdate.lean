import CppFormalization.Cpp2.RuntimeModel.RuntimeDeclUpdate
import CppFormalization.Cpp2.RuntimeModel.Facts.RuntimeState

namespace Cpp

/-!
# CppFormalization.Cpp2.Core.Facts.RuntimeDeclUpdate

Facts specific to declareObjectStateCore / declareObjectStateWithNext and the
declaration-update surface.
-/


/-!
Runtime lemmas for declaration-state updates.

Primitive state-operation algebra, including `setNext`, `writeHeap`,
`bindTopBinding`, and `recordLocal`, belongs in `Core.Facts.RuntimeState`.

This file contains facts specific to:
* `declareObjectStateCore`
* `declareObjectStateWithNext`
* the legacy `declareObjectState` façade
* `declareRefState`

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

/-! ## Legacy object declaration façade -/

@[simp] theorem next_declareObjectState
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).next = σ.next + 1 := by
  simp [declareObjectState, declareObjectStateWithNext, setNext]

@[simp] theorem declareObjectState_next
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).next = σ.next + 1 := by
  simp

@[simp] theorem heap_declareObjectState_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  simp [declareObjectState, declareObjectStateWithNext, setNext, declareObjectStateCore]

@[simp] theorem declareObjectState_heap_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  simp [heap_declareObjectState_self σ τ x ov]

@[simp] theorem heap_declareObjectState_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (b : Nat) (hb : b ≠ σ.next) :
    (declareObjectState σ τ x ov).heap b = σ.heap b := by
  simp [declareObjectState, declareObjectStateWithNext, setNext,
    declareObjectStateCore, hb]

@[simp] theorem declareObjectState_heap_other
    (σ : State) {a : Nat} (τ : CppType) (x : Ident) (ov : Option Value)
    (ha : a ≠ σ.next) :
    (declareObjectState σ τ x ov).heap a = σ.heap a := by
  exact heap_declareObjectState_other σ τ x ov a ha

@[simp] theorem declareObjectState_scopes_ne_nil
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).scopes ≠ [] := by
  unfold declareObjectState declareObjectStateWithNext setNext declareObjectStateCore
  simp [scopes_recordLocal, scopes_writeHeap, scopes_bindTopBinding]
  cases σ.scopes <;> simp

@[simp] theorem declareObjectState_top_local_mem
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    match (declareObjectState σ τ x ov).scopes with
    | [] => False
    | fr :: _ => σ.next ∈ fr.locals := by
  unfold declareObjectState declareObjectStateWithNext setNext declareObjectStateCore
  simp [scopes_recordLocal, scopes_writeHeap, scopes_bindTopBinding]
  cases σ.scopes <;> simp

@[simp] theorem lookupBinding_declareObjectState_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    lookupBinding (declareObjectState σ τ x ov) x = some (.object τ σ.next) := by
  simp [declareObjectState, declareObjectStateWithNext, declareObjectStateCore]

@[simp] theorem lookupBinding_declareObjectState_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (hxy : y ≠ x) :
    lookupBinding (declareObjectState σ τ x ov) y = lookupBinding σ y := by
  unfold declareObjectState declareObjectStateWithNext declareObjectStateCore
  simp [hxy]

@[simp] theorem declareObjectState_scopes_succ
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {k : Nat} :
    (declareObjectState σ τ x ov).scopes[k.succ]? = σ.scopes[k.succ]? := by
  unfold declareObjectState declareObjectStateWithNext setNext declareObjectStateCore
  cases hsc : σ.scopes with
  | nil =>
      simp [ recordLocal, bindTopBinding, writeHeap, hsc]
  | cons fr0 frs =>
      simp [ recordLocal, bindTopBinding, writeHeap, hsc]

@[simp] theorem declareObjectState_scopes_zero_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs) :
    (declareObjectState σ τ x ov).scopes[0]? =
      some
        { fr0 with
          binds := fun y => if y = x then some (.object τ σ.next) else fr0.binds y
          locals := σ.next :: fr0.locals } := by
  unfold declareObjectState declareObjectStateWithNext setNext declareObjectStateCore
  simp [recordLocal, bindTopBinding, writeHeap, hsc]

@[simp] theorem declareObjectState_scopes_zero_of_nil
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hsc : σ.scopes = []) :
    (declareObjectState σ τ x ov).scopes[0]? =
      some
        { binds := fun y => if y = x then some (.object τ σ.next) else none
          locals := [σ.next] } := by
  unfold declareObjectState declareObjectStateWithNext setNext declareObjectStateCore
  simp [recordLocal, bindTopBinding, writeHeap, hsc]

@[simp] theorem declareObjectState_lookup_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {k : Nat} {fr : ScopeFrame} :
    (declareObjectState σ τ x ov).scopes[k.succ]? = some fr ↔
      σ.scopes[k.succ]? = some fr := by
  unfold declareObjectState declareObjectStateWithNext setNext declareObjectStateCore
  simp [recordLocal, bindTopBinding, writeHeap]
  cases hsc : σ.scopes with
  | nil =>
    simp
  | cons fr0 frs =>
    simp

theorem declareObjectState_lookup_zero_frame_of_nil
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hsc : σ.scopes = [])
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    fr =
      { binds := fun y => if y = x then some (.object τ σ.next) else none
        locals := [σ.next] } := by
  simp [declareObjectState_scopes_zero_of_nil hsc] at hk
  exact hk.symm

theorem declareObjectState_lookup_zero_frame_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    fr =
      { fr0 with
        binds := fun y => if y = x then some (.object τ σ.next) else fr0.binds y
        locals := σ.next :: fr0.locals } := by
  simp [declareObjectState_scopes_zero_of_cons hsc] at hk
  exact hk.symm

theorem declareObjectState_lookup_zero_locals_of_nil
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hsc : σ.scopes = [])
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    fr.locals = [σ.next] := by
  rcases declareObjectState_lookup_zero_frame_of_nil
      (σ := σ) (τ := τ) (x := x) (ov := ov) hsc hk with rfl
  simp

theorem declareObjectState_lookup_zero_locals_of_cons
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareObjectState σ τ x ov).scopes[0]? = some fr) :
    fr.locals = σ.next :: fr0.locals := by
  rcases declareObjectState_lookup_zero_frame_of_cons hsc hk with rfl
  simp

theorem mem_declareObjectState_top_locals_iff
    {fr : ScopeFrame} {a b : Nat} {x : Ident} {τ : CppType} :
    a ∈ ({ fr with
      binds := fun y => if y = x then some (.object τ b) else fr.binds y,
      locals := b :: fr.locals }).locals
    ↔ a = b ∨ a ∈ fr.locals := by
  simp

/-! ## Reference declaration update -/

@[simp] theorem next_declareRefState
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    (declareRefState σ τ x a).next = σ.next := by
  unfold declareRefState
  simp

@[simp] theorem declareRefState_next
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    (declareRefState σ τ x a).next = σ.next := by
  simp

@[simp] theorem scopes_declareRefState
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    (declareRefState σ τ x a).scopes =
      match σ.scopes with
      | [] => [{ binds := fun y => if y = x then some (.ref τ a) else none, locals := [] }]
      | fr :: frs =>
          { fr with binds := fun y => if y = x then some (.ref τ a) else fr.binds y } :: frs := by
  unfold declareRefState
  simp only [scopes_bindTopBinding σ x (.ref τ a)]
  rfl

@[simp] theorem heap_declareRefState
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    (declareRefState σ τ x a).heap = σ.heap := by
  unfold declareRefState
  simp [heap_bindTopBinding]

@[simp] theorem declareRefState_heap
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    (declareRefState σ τ x a).heap = σ.heap := by
  simp

@[simp] theorem declareRefState_scopes_ne_nil
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    (declareRefState σ τ x a).scopes ≠ [] := by
  unfold declareRefState bindTopBinding
  split <;> simp

@[simp] theorem lookupBinding_declareRefState_self
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    lookupBinding (declareRefState σ τ x a) x = some (.ref τ a) := by
  unfold declareRefState
  simp

@[simp] theorem lookupBinding_declareRefState_other
    (σ : State) (τ : CppType) (x y : Ident) (a : Nat) (hxy : y ≠ x) :
    lookupBinding (declareRefState σ τ x a) y = lookupBinding σ y := by
  unfold declareRefState
  simp [hxy]

/-- `declareRefState` only changes the top frame; deeper scopes are untouched. -/
@[simp] theorem declareRefState_scopes_succ
    {σ : State} {τ : CppType} {x : Ident} {a : Nat} {k : Nat} :
    (declareRefState σ τ x a).scopes[k.succ]? = σ.scopes[k.succ]? := by
  cases hsc : σ.scopes <;> simp [declareRefState, scopes_bindTopBinding, hsc]

@[simp] theorem declareRefState_lookup_succ_iff
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {fr : ScopeFrame} :
    (declareRefState σ τ x a).scopes[k.succ]? = some fr ↔
      σ.scopes[k.succ]? = some fr := by
  rw [declareRefState_scopes_succ]

@[simp] theorem declareRefState_scopes_zero_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs) :
    (declareRefState σ τ x a).scopes[0]? =
      some
        { fr0 with
          binds := fun y => if y = x then some (.ref τ a) else fr0.binds y } := by
  simp [declareRefState, scopes_bindTopBinding, hsc]

theorem declareRefState_lookup_zero_frame_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[0]? = some fr) :
    fr =
      { fr0 with
        binds := fun y => if y = x then some (.ref τ a) else fr0.binds y } := by
  rw [declareRefState_scopes_zero_of_cons hsc] at hk
  injection hk with h_eq
  exact h_eq.symm

theorem declareRefState_lookup_zero_locals_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[0]? = some fr) :
    fr.locals = fr0.locals := by
  rcases declareRefState_lookup_zero_frame_of_cons hsc hk with rfl
  simp

theorem declareRefState_lookup_preserves_locals_forward
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {fr : ScopeFrame}
    (hk : σ.scopes[k]? = some fr) :
    ∃ fr',
      (declareRefState σ τ x a).scopes[k]? = some fr' ∧
      fr'.locals = fr.locals := by
  cases k with
  | zero =>
      cases hsc : σ.scopes with
      | nil =>
          simp [hsc] at hk
      | cons fr0 frs =>
          simp [hsc] at hk
          subst fr
          refine ⟨
            { fr0 with
              binds := fun y => if y = x then some (.ref τ a) else fr0.binds y },
            ?_,
            rfl⟩
          exact declareRefState_scopes_zero_of_cons hsc
  | succ k =>
      refine ⟨fr, ?_, rfl⟩
      exact (declareRefState_lookup_succ_iff).2 hk

theorem declareRefState_lookup_preserves_locals_backward_of_cons
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr0 : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr0 :: frs)
    {k : Nat} {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[k]? = some fr) :
    ∃ fr',
      σ.scopes[k]? = some fr' ∧
      fr.locals = fr'.locals := by
  cases k with
  | zero =>
      refine ⟨fr0, by simp [hsc], ?_⟩
      exact declareRefState_lookup_zero_locals_of_cons hsc hk
  | succ k =>
      refine ⟨fr, ?_, rfl⟩
      exact (declareRefState_lookup_succ_iff).1 hk

end Cpp
