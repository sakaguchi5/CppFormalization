import CppFormalization.Cpp2.RuntimeModel.RuntimeOps

namespace Cpp

/-!
# CppFormalization.Cpp2.Core.Facts.RuntimeState

Core-level facts about primitive runtime-state operations.

This file must stay below Semantics: it talks about State, primitive runtime
updates, heap/scope lookup algebra, and scope-closing support, but not
BigStepStmt/OpenScope/CloseScope as semantic relations.

Declaration-state update facts for `declareObjectStateCore`,
`declareObjectStateWithNext`, `declareObjectState`, and `declareRefState` belong
in `Core.Facts.RuntimeDeclUpdate`.
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

/-- Top-frame binding update does not change `locals`. -/
@[simp] theorem locals_bindTopBinding_top
    {fr : ScopeFrame} {x : Ident} {b : Binding} :
    ({ fr with binds := fun y => if y = x then some b else fr.binds y }).locals = fr.locals := by
  rfl

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

@[simp] theorem locals_recordLocal_top
    {fr : ScopeFrame} {x : Ident} {b : Binding} {a : Nat} :
    ({ fr with
        binds := fun y => if y = x then some b else fr.binds y
        locals := a :: fr.locals }).locals
      = a :: fr.locals := by
  rfl

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
      simp at ha
      have hal : a ≠ l := ha.left
      have ha_ls : a ∉ ls := ha.right

      rw [ih (σ := killAddr σ l) ha_ls]
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
