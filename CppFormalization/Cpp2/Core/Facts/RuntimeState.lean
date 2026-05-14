import CppFormalization.Cpp2.Core.RuntimeDeclUpdate

namespace Cpp

/-!
# CppFormalization.Cpp2.Core.Facts.RuntimeState

Core-level facts about primitive runtime-state operations.

This file must stay below Semantics: it talks about State, runtime updates, heap/scope lookup algebra, and declaration-state update definitions, but not BigStepStmt/OpenScope/CloseScope as semantic relations.
-/


/-!
Primitive state/update lemmas and scope-closing support.
-/

/-!  Heap/state lookup algebra: primitive operations first. -/

@[simp] theorem lookupBinding_pushScope (σ : State) (x : Ident) :
    lookupBinding (pushScope σ) x = lookupBinding σ x := by
  rfl

@[simp] theorem currentScopeFresh_pushScope
    (σ : State) (x : Ident) :
    currentScopeFresh (pushScope σ) x := by
  unfold currentScopeFresh pushScope emptyScopeFrame
  simp

@[simp] theorem heap_pushScope
    (σ : State) :
    (pushScope σ).heap = σ.heap := by
  rfl

@[simp] theorem next_pushScope
    (σ : State) :
    (pushScope σ).next = σ.next := by
  rfl

@[simp] theorem next_setNext (σ : State) (a : Nat) :
    (setNext σ a).next = a := by
  rfl

@[simp] theorem scopes_setNext (σ : State) (a : Nat) :
    (setNext σ a).scopes = σ.scopes := by
  rfl

@[simp] theorem heap_setNext (σ : State) (a : Nat) :
    (setNext σ a).heap = σ.heap := by
  rfl

@[simp] theorem lookupBinding_setNext
    (σ : State) (n : Nat) (x : Ident) :
    lookupBinding (setNext σ n) x = lookupBinding σ x := by
  rfl

@[simp] theorem lookupBinding_record_next
    (σ : State) (n : Nat) (x : Ident) :
    lookupBinding ({ σ with next := n }) x = lookupBinding σ x := by
  rfl

/-- Heap writes do not change the runtime scope stack. -/
@[simp] theorem scopes_writeHeap
    (σ : State) (a : Nat) (c : Cell) :
    (writeHeap σ a c).scopes = σ.scopes := by
  rfl

/-- Heap writes do not change the runtime cursor. -/
@[simp] theorem next_writeHeap
    (σ : State) (a : Nat) (c : Cell) :
    (writeHeap σ a c).next = σ.next := by
  rfl

@[simp] theorem lookupBinding_writeHeap
    (σ : State) (a : Nat) (c : Cell) (x : Ident) :
    lookupBinding (writeHeap σ a c) x = lookupBinding σ x := by
  rfl

@[simp] theorem lookupBinding_bindTopBinding_self
    (σ : State) (x : Ident) (b : Binding) :
    lookupBinding (bindTopBinding σ x b) x = some b := by
  unfold lookupBinding bindTopBinding
  cases σ.scopes <;>
    simp [lookupBindingFrames]

@[simp] theorem lookupBinding_bindTopBinding_other
    (σ : State) {x y : Ident} (b : Binding) (hxy : y ≠ x) :
    lookupBinding (bindTopBinding σ x b) y = lookupBinding σ y := by
  unfold lookupBinding bindTopBinding
  cases σ.scopes <;>
    simp [lookupBindingFrames, hxy]

@[simp] theorem scopes_bindTopBinding
    (σ : State) (x : Ident) (b : Binding) :
    (bindTopBinding σ x b).scopes =
      match σ.scopes with
      | [] => [{ binds := fun y => if y = x then some b else none, locals := [] }]
      | fr :: frs =>
          { fr with binds := fun y => if y = x then some b else fr.binds y } :: frs := by
  unfold bindTopBinding
  cases σ.scopes <;> rfl

/-- Binding in the top frame does not change the runtime cursor. -/
@[simp] theorem next_bindTopBinding
    (σ : State) (x : Ident) (b : Binding) :
    (bindTopBinding σ x b).next = σ.next := by
  unfold bindTopBinding
  split <;> rfl

@[simp] theorem heap_bindTopBinding
    (σ : State) (x : Ident) (bnd : Binding) :
    (bindTopBinding σ x bnd).heap = σ.heap := by
  unfold bindTopBinding
  split <;> rfl

@[simp] theorem scopes_recordLocal
    (σ : State) (a : Nat) :
    (recordLocal σ a).scopes =
      match σ.scopes with
      | [] => []
      | fr :: frs => { fr with locals := a :: fr.locals } :: frs := by
  unfold recordLocal
  cases h : σ.scopes <;> simp [h]

@[simp] theorem heap_recordLocal
    (σ : State) (a : Nat) :
    (recordLocal σ a).heap = σ.heap := by
  unfold recordLocal
  split <;> rfl

/-- Recording a local address does not change the runtime cursor. -/
@[simp] theorem next_recordLocal
    (σ : State) (a : Nat) :
    (recordLocal σ a).next = σ.next := by
  unfold recordLocal
  split <;> rfl

@[simp] theorem lookupBinding_recordLocal
    (σ : State) (a : Nat) (x : Ident) :
    lookupBinding (recordLocal σ a) x = lookupBinding σ x := by
  unfold recordLocal lookupBinding
  split
  · simp
  · rename_i fr frs h_scopes
    unfold lookupBindingFrames
    simp [h_scopes]

/-- Killing one address does not change the runtime scope stack. -/
@[simp] theorem scopes_killAddr
    (σ : State) (a : Nat) :
    (killAddr σ a).scopes = σ.scopes := by
  unfold killAddr
  split <;> simp [writeHeap]

@[simp] theorem next_killAddr
    (σ : State) (a : Nat) :
    (killAddr σ a).next = σ.next := by
  unfold killAddr
  split <;> simp [writeHeap]

/-- Killing locals only changes heap liveness; it does not change the scope stack. -/
@[simp] theorem scopes_killLocals
    (σ : State) (ls : List Nat) :
    (killLocals σ ls).scopes = σ.scopes := by
  induction ls generalizing σ with
  | nil =>
      rfl
  | cons a ls ih =>
      simp [killLocals, ih]

@[simp] theorem next_killLocals
    (σ : State) (ls : List Nat) :
    (killLocals σ ls).next = σ.next := by
  induction ls generalizing σ with
  | nil =>
      rfl
  | cons a ls ih =>
      simp [killLocals, ih]

@[simp] theorem heap_writeHeap_self
    (σ : State) (a : Nat) (c : Cell) :
    (writeHeap σ a c).heap a = some c := by
  unfold writeHeap
  simp

@[simp] theorem heap_writeHeap_other
    (σ : State) (a b : Nat) (c : Cell) (hab : b ≠ a) :
    (writeHeap σ a c).heap b = σ.heap b := by
  unfold writeHeap
  simp [hab]

@[simp] theorem writeHeap_eq
    (σ : State) (a : Nat) (c : Cell) :
    (writeHeap σ a c).heap a = some c := by
  simp

@[simp] theorem writeHeap_ne
    (σ : State) {a b : Nat} (c : Cell) (h : b ≠ a) :
    (writeHeap σ a c).heap b = σ.heap b := by
  exact heap_writeHeap_other σ a b c h

/-!  Declaration/update operations. -/

@[simp] theorem next_declareObjectState
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).next = σ.next + 1 := by
  simp [declareObjectState, declareObjectStateWithNext, setNext]

@[simp] theorem declareObjectState_next
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).next = σ.next + 1 := by
  simp

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
  --cases h : σ.scopes <;> simp [h]
  cases σ.scopes <;> simp

@[simp] theorem declareObjectState_top_local_mem
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    match (declareObjectState σ τ x ov).scopes with
    | [] => False
    | fr :: _ => σ.next ∈ fr.locals := by
  unfold declareObjectState declareObjectStateWithNext setNext declareObjectStateCore
  simp [scopes_recordLocal, scopes_writeHeap, scopes_bindTopBinding]
  --cases h : σ.scopes <;> simp [h]
  cases σ.scopes <;> simp

@[simp] theorem lookupBinding_eq_of_scopes_eq
    {σ₁ σ₂ : State} (h : σ₁.scopes = σ₂.scopes) (x : Ident) :
    lookupBinding σ₁ x = lookupBinding σ₂ x := by
  cases σ₁
  cases σ₂
  cases h
  rfl

@[simp] theorem lookupBinding_killAddr
    (σ : State) (a : Nat) (x : Ident) :
    lookupBinding (killAddr σ a) x = lookupBinding σ x := by
  exact lookupBinding_eq_of_scopes_eq (scopes_killAddr σ a) x

@[simp] theorem lookupBinding_killLocals
    (σ : State) (ls : List Nat) (x : Ident) :
    lookupBinding (killLocals σ ls) x = lookupBinding σ x := by
  exact lookupBinding_eq_of_scopes_eq (scopes_killLocals σ ls) x

@[simp] theorem lookupBinding_declareObjectState_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    lookupBinding (declareObjectState σ τ x ov) x = some (.object τ σ.next) := by
  simp [declareObjectState, declareObjectStateWithNext, declareObjectStateCore]

@[simp] theorem lookupBinding_declareRefState_self
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    lookupBinding (declareRefState σ τ x a) x = some (.ref τ a) := by
  unfold declareRefState
  simp

@[simp] theorem lookupBinding_declareObjectState_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value)
    (hxy : y ≠ x) :
    lookupBinding (declareObjectState σ τ x ov) y = lookupBinding σ y := by
  unfold declareObjectState declareObjectStateWithNext declareObjectStateCore
  simp [hxy]

@[simp] theorem lookupBinding_declareRefState_other
    (σ : State) (τ : CppType) (x y : Ident) (a : Nat) (hxy : y ≠ x) :
    lookupBinding (declareRefState σ τ x a) y = lookupBinding σ y := by
  unfold declareRefState
  simp [hxy]

/-!  Scope-closing support lemmas. -/

@[simp] theorem heap_killAddr_other
    (σ : State) (a b : Nat) (h : b ≠ a) :
    (killAddr σ a).heap b = σ.heap b := by
  unfold killAddr
  split
  · rfl
  · rw [heap_writeHeap_other]
    exact h

@[simp] theorem heap_killLocals_other
    (σ : State) (ls : List Nat) (a : Nat) (ha : a ∉ ls) :
    (killLocals σ ls).heap a = σ.heap a := by
  induction ls generalizing σ with
  | nil =>
      unfold killLocals
      rfl
  | cons l ls ih =>
      unfold killLocals
      -- ha : a ∉ l :: ls を分解してそれぞれの事実を取り出す
      simp at ha
      have hal : a ≠ l := ha.left
      have ha_ls : a ∉ ls := ha.right

      -- 1. 再帰呼び出しの部分を書き換え
      rw [ih (σ := killAddr σ l) ha_ls]
      -- 2. killAddr に関する補題を適用
      exact heap_killAddr_other σ l a hal

theorem popScope?_some_scopes
    (σ σ' : State) :
    popScope? σ = some σ' →
    ∃ fr frs, σ.scopes = fr :: frs := by
  cases h : σ.scopes <;> simp [popScope?, h]

@[simp] theorem popScope?_pushScope
    (σ : State) :
    popScope? (pushScope σ) = some σ := by
  unfold pushScope popScope?
  unfold emptyScopeFrame
  simp only
  unfold killLocals
  simp

@[simp] theorem popScope?_none_iff
    (σ : State) :
    popScope? σ = none ↔ σ.scopes = [] := by
  cases h : σ.scopes <;> simp [popScope?, h]

@[simp] theorem popScope?_some_iff
    (σ : State) :
    (∃ σ', popScope? σ = some σ') ↔ σ.scopes ≠ [] := by
  cases h : σ.scopes <;> simp [popScope?, h]

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
  -- あとは、(x :: xs)[k.succ]? = xs[k]? という List の基本性質に帰着
  cases hsc : σ.scopes with
  | nil =>
    -- σ.scopes = [] の場合、左辺も右辺も none になり、some fr とは一致しないので矛盾で終わる
    simp
  | cons fr0 frs =>
    -- σ.scopes = fr0 :: frs の場合、両辺とも frs[k]? = some fr になる
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

@[simp] theorem locals_recordLocal_top
    {fr : ScopeFrame} {x : Ident} {b : Binding} {a : Nat} :
    ({ fr with
        binds := fun y => if y = x then some b else fr.binds y
        locals := a :: fr.locals }).locals
      = a :: fr.locals := by
  rfl

theorem mem_declareObjectState_top_locals_iff
    {fr : ScopeFrame} {a b : Nat} {x : Ident} {τ : CppType} :
    a ∈ ({ fr with
      binds := fun y => if y = x then some (.object τ b) else fr.binds y,
      locals := b :: fr.locals }).locals
    ↔ a = b ∨ a ∈ fr.locals := by
  simp

/-- Top-frame binding update does not change `locals`. -/
@[simp] theorem locals_bindTopBinding_top
    {fr : ScopeFrame} {x : Ident} {b : Binding} :
    ({ fr with binds := fun y => if y = x then some b else fr.binds y }).locals = fr.locals := by
  rfl

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

/--
`bindTopBinding` only changes the binding map of the top frame.
It never creates owned locals.  If it creates a frame from an empty stack,
that new frame has empty locals; otherwise every resulting frame has the
same `locals` list as the corresponding old frame.
-/
theorem bindTopBinding_scope_locals_empty_or_old
    {σ : State} {x : Ident} {b : Binding} {k : Nat} {fr : ScopeFrame}
    (h : (bindTopBinding σ x b).scopes[k]? = some fr) :
    fr.locals = [] ∨
      ∃ fr₀, σ.scopes[k]? = some fr₀ ∧ fr.locals = fr₀.locals := by
  cases hσ : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [bindTopBinding, hσ] at h
          subst fr
          exact Or.inl rfl
      | succ k =>
          simp [bindTopBinding, hσ] at h
  | cons fr₀ frs =>
      cases k with
      | zero =>
          simp [bindTopBinding, hσ] at h
          subst fr
          exact Or.inr ⟨fr₀, by simp , rfl⟩
      | succ k =>
          simp [bindTopBinding, hσ] at h
          exact Or.inr ⟨fr, by simpa [hσ] using h, rfl⟩

/--
`pushScope` creates one new empty top frame.  Every non-top frame in the
post-state is an old frame shifted by one index, with the same `locals`.
-/
theorem pushScope_scope_locals_empty_or_old
    {σ : State} {k : Nat} {fr : ScopeFrame}
    (h : (pushScope σ).scopes[k]? = some fr) :
    fr.locals = [] ∨
      ∃ (k₀ : Nat) (fr₀ : ScopeFrame),
        k = Nat.succ k₀ ∧
        σ.scopes[k₀]? = some fr₀ ∧
        fr.locals = fr₀.locals := by
  cases k with
  | zero =>
      simp [pushScope, emptyScopeFrame] at h
      subst fr
      exact Or.inl rfl
  | succ k =>
      have hk : σ.scopes[k]? = some fr := by
        simpa [pushScope] using h
      exact Or.inr ⟨k, fr, rfl, hk, rfl⟩


end Cpp
