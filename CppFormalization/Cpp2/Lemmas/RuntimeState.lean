import CppFormalization.Cpp2.Semantics.Stmt

/-!
Primitive state/update lemmas and scope-closing support.
-/

namespace Cpp

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

@[simp] theorem lookupBinding_setNext
    (σ : State) (n : Nat) (x : Ident) :
    lookupBinding ({ σ with next := n }) x = lookupBinding σ x := by
  rfl

@[simp] theorem scopes_writeHeap
    (σ : State) (a : Nat) (c : Cell) :
    (writeHeap σ a c).scopes = σ.scopes := by
  rfl
/-
@[simp] theorem next_writeHeap
    (σ : State) (a : Nat) (c : Cell) :
    (writeHeap σ a c).next = σ.next := by
  rfl
-/
@[simp] theorem lookupBinding_writeHeap
    (σ : State) (a : Nat) (c : Cell) (x : Ident) :
    lookupBinding (writeHeap σ a c) x = lookupBinding σ x := by
  rfl

@[simp] theorem lookupBinding_bindTopBinding_self
    (σ : State) (x : Ident) (b : Binding) :
    lookupBinding (bindTopBinding σ x b) x = some b := by
  unfold lookupBinding bindTopBinding lookupBindingFrames
  cases hsc : σ.scopes with
  | nil =>
      simp
  | cons fr frs =>
      simp

@[simp] theorem lookupBinding_bindTopBinding_other
    (σ : State) {x y : Ident} (b : Binding) (hxy : y ≠ x) :
    lookupBinding (bindTopBinding σ x b) y = lookupBinding σ y := by
  unfold lookupBinding bindTopBinding lookupBindingFrames
  cases hsc : σ.scopes with
  | nil =>
      simp only
      unfold lookupBindingFrames
      simp [hxy]
  | cons fr frs =>
      simp [hxy]

@[simp] theorem scopes_bindTopBinding
    (σ : State) (x : Ident) (b : Binding) :
    (bindTopBinding σ x b).scopes =
      match σ.scopes with
      | [] => [{ binds := fun y => if y = x then some b else none, locals := [] }]
      | fr :: frs =>
          { fr with binds := fun y => if y = x then some b else fr.binds y } :: frs := by
  unfold bindTopBinding
  cases σ.scopes <;> rfl
/-
@[simp] theorem next_bindTopBinding
    (σ : State) (x : Ident) (b : Binding) :
    (bindTopBinding σ x b).next = σ.next := by
  unfold bindTopBinding
  split <;> rfl
-/
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
/-
@[simp] theorem next_recordLocal
    (σ : State) (a : Nat) :
    (recordLocal σ a).next = σ.next := by
  unfold recordLocal
  split <;> rfl
-/
@[simp] theorem lookupBinding_recordLocal
    (σ : State) (a : Nat) (x : Ident) :
    lookupBinding (recordLocal σ a) x = lookupBinding σ x := by
  unfold recordLocal lookupBinding
  split
  · simp
  · rename_i fr frs h_scopes
    unfold lookupBindingFrames
    simp [h_scopes]

@[simp] theorem scopes_killAddr
    (σ : State) (a : Nat) :
    (killAddr σ a).scopes = σ.scopes := by
  unfold killAddr
  split
  · rfl
  · unfold writeHeap
    rfl

@[simp] theorem next_killAddr
    (σ : State) (a : Nat) :
    (killAddr σ a).next = σ.next := by
  unfold killAddr
  split
  · rfl
  · unfold writeHeap
    rfl

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
  simpa using heap_writeHeap_other σ a b c h

/-!  Declaration/update operations. -/

@[simp] theorem next_declareObjectState
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).next = σ.next + 1 := by
  unfold declareObjectState recordLocal bindTopBinding writeHeap
  split <;> simp

@[simp] theorem declareObjectState_next
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).next = σ.next + 1 := by
  simp

@[simp] theorem next_declareRefState
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    (declareRefState σ τ x a).next = σ.next := by
  unfold declareRefState bindTopBinding
  split <;> simp

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
  unfold declareObjectState recordLocal bindTopBinding writeHeap
  simp only
  split <;> simp

@[simp] theorem declareObjectState_heap_self
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).heap σ.next =
      some { ty := τ, value := ov, alive := true } := by
  simp [heap_declareObjectState_self σ τ x ov]

@[simp] theorem heap_declareObjectState_other
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value)
    (b : Nat) (hb : b ≠ σ.next) :
    (declareObjectState σ τ x ov).heap b = σ.heap b := by
  unfold declareObjectState recordLocal
  simp
  split <;> simp [heap_writeHeap_other _ _ _ _ hb]

@[simp] theorem declareObjectState_heap_other
    (σ : State) {a : Nat} (τ : CppType) (x : Ident) (ov : Option Value)
    (ha : a ≠ σ.next) :
    (declareObjectState σ τ x ov).heap a = σ.heap a := by
  simpa using heap_declareObjectState_other σ τ x ov a ha

@[simp] theorem declareObjectState_scopes_ne_nil
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    (declareObjectState σ τ x ov).scopes ≠ [] := by
  unfold declareObjectState recordLocal bindTopBinding
  split <;> simp

@[simp] theorem declareObjectState_top_local_mem
    (σ : State) (τ : CppType) (x : Ident) (ov : Option Value) :
    match (declareObjectState σ τ x ov).scopes with
    | [] => False
    | fr :: _ => σ.next ∈ fr.locals := by
  -- 1. 本体の定義だけを開く
  unfold declareObjectState
  -- 2. recordLocal や writeHeap の定義を直接開かず、
  --    既に証明した「性質（定理）」を simp に与えて簡約させる
  simp [scopes_recordLocal, scopes_writeHeap, scopes_bindTopBinding]
  -- 3. この時点で match σ.scopes with ... が外側に来るので、cases で分解する
  cases h : σ.scopes <;> simp

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
  unfold declareObjectState
  rw [lookupBinding_recordLocal]
  rw [lookupBinding_writeHeap]
  let σ' : State :=
    { scopes := (bindTopBinding σ x (.object τ σ.next)).scopes
    , heap   := (bindTopBinding σ x (.object τ σ.next)).heap
    , next   := σ.next + 1
    }
  change lookupBinding σ' x = some (.object τ σ.next)
  calc
    lookupBinding σ' x
        = lookupBinding (bindTopBinding σ x (.object τ σ.next)) x := by
            exact lookupBinding_eq_of_scopes_eq
              (σ₁ := σ')
              (σ₂ := bindTopBinding σ x (.object τ σ.next))
              (h := rfl)
              (x := x)
    _ = some (.object τ σ.next) := by
          simp [(lookupBinding_bindTopBinding_self
              (σ := σ) (x := x) (b := .object τ σ.next))]

@[simp] theorem lookupBinding_declareRefState_self
    (σ : State) (τ : CppType) (x : Ident) (a : Nat) :
    lookupBinding (declareRefState σ τ x a) x = some (.ref τ a) := by
  unfold declareRefState
  simp

@[simp] theorem lookupBinding_declareObjectState_other
    (σ : State) (τ : CppType) (x y : Ident) (ov : Option Value) (hxy : y ≠ x) :
    lookupBinding (declareObjectState σ τ x ov) y = lookupBinding σ y := by
  unfold declareObjectState
  rw [lookupBinding_recordLocal]
  rw [lookupBinding_writeHeap]
  let σ' : State :=
    { scopes := (bindTopBinding σ x (.object τ σ.next)).scopes
    , heap   := (bindTopBinding σ x (.object τ σ.next)).heap
    , next   := σ.next + 1
    }
  change lookupBinding σ' y = lookupBinding σ y
  calc
    lookupBinding σ' y
        = lookupBinding (bindTopBinding σ x (.object τ σ.next)) y := by
            exact lookupBinding_eq_of_scopes_eq
              (σ₁ := σ')
              (σ₂ := bindTopBinding σ x (.object τ σ.next))
              (h := rfl)
              (x := y)
    _ = lookupBinding σ y := by
          simpa using
            (lookupBinding_bindTopBinding_other
              (σ := σ) (x := x) (y := y) (b := .object τ σ.next) hxy)

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
      simp
  | cons l ls ih =>
      unfold killLocals
      have ha_ls : a ∉ ls := by
        simp at ha
        exact ha.right
      rw [ih (σ := killAddr σ l) ha_ls]
      have hal : a ≠ l := by
        intro h
        subst h
        simp at ha
      simpa [Ne.symm hal] using heap_killAddr_other σ l a hal

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
  rw [← Option.isSome_iff_exists]
  rw [Option.isSome_iff_ne_none]
  simp [popScope?_none_iff]

@[simp] theorem openScope_eq
    {σ σ' : State} :
    OpenScope σ σ' ↔ σ' = pushScope σ := by
  rfl

@[simp] theorem openScope_eq_pushScope
    {σ σ' : State} :
    OpenScope σ σ' ↔ σ' = pushScope σ := by
  simp

@[simp] theorem closeScope_eq
    {σ σ' : State} :
    CloseScope σ σ' ↔ popScope? σ = some σ' := by
  rfl

@[simp] theorem closeScope_eq_popScope
    {σ σ' : State} :
    CloseScope σ σ' ↔ popScope? σ = some σ' := by
  simp

end Cpp
