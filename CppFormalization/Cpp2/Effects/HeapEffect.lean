import CppFormalization.Cpp2.Effects.NormalHeadContext
import CppFormalization.Cpp2.Core.Facts.RuntimeState
import CppFormalization.Cpp2.Core.Facts.RuntimeDeclUpdate

namespace Cpp

/-!
# CppFormalization.Cpp2.Effects.HeapEffect

Axiom-free heap/runtime effect vocabulary for primitive normal heads.

Important Lean design note:
`BigStepStmt`, `Assigns`, and `DeclaresObject` are `Prop`.  Therefore we should
not try to define a computational function extracting `Value`, addresses, or
states from them.  The concrete effect records that carry such data live in
`Type`; extraction statements return `Nonempty ...`, which is a `Prop` saying
that such a data-carrying certificate exists.
-/

/-- The heap component is unchanged. -/
structure HeapUnchanged (σ σ' : State) : Prop where
  heapEq : σ'.heap = σ.heap

/--
A normal assignment writes exactly one concrete heap address.

This is a data-carrying certificate, so it must live in `Type`, not `Prop`.
A proposition-valued structure may only have proof fields.
-/
structure AssignHeapWriteEffect
    (σ σ' : State) (p : PlaceExpr) (e : ValExpr) : Type where
  value : Value
  addr : Nat
  oldCell : Cell
  eval : BigStepValue σ e value
  place : BigStepPlace σ p addr
  oldCellAt : σ.heap addr = some oldCell
  oldLive : oldCell.alive = true
  valueCompat : ValueCompat value oldCell.ty
  postState : σ' = writeHeap σ addr { oldCell with value := some value }

/--
Object declaration exposes its lower semantic payload/cursor split.

This also carries data (`postCursor`, `coreState`), so it is `Type`.
-/
structure ObjectDeclHeapIntroEffect
    (σ σ' : State) (τ : CppType) (x : Ident) (ov : Option Value) : Type where
  postCursor : Nat
  coreState : State
  payload : DeclaresObjectPayload σ τ x ov coreState
  cursorPolicy : DeclaresObjectCursorPolicy coreState postCursor σ'

/-- Reference declaration introduces a top-frame reference binding to an existing live cell. -/
structure RefDeclBindingEffect
    (σ σ' : State) (τ : CppType) (x : Ident) (a : Nat) : Prop where
  fresh : currentScopeFresh σ x
  targetCell : ∃ c, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true
  postState : σ' = declareRefState σ τ x a

/-! ## Effects extracted from operational steps -/

theorem heapUnchanged_of_skip_step
    {σ σ' : State} :
    BigStepStmt σ .skip .normal σ' → HeapUnchanged σ σ' := by
  intro h
  cases h
  exact ⟨rfl⟩

theorem heapUnchanged_of_exprStmt_step
    {σ σ' : State} {e : ValExpr} :
    BigStepStmt σ (.exprStmt e) .normal σ' → HeapUnchanged σ σ' := by
  intro h
  cases h
  exact ⟨rfl⟩

/--
Existence of the assignment write certificate.

The result is `Nonempty ...`, hence still a `Prop`.  This lets us eliminate the
operational `Prop` proof while the witness type itself may carry `Value`/`Nat`
data.
-/
theorem nonempty_assignHeapWriteEffect_of_step
    {σ σ' : State} {p : PlaceExpr} {e : ValExpr} :
    BigStepStmt σ (.assign p e) .normal σ' →
    Nonempty (AssignHeapWriteEffect σ σ' p e) := by
  intro h
  cases h with
  | assign hval hassign =>
      rcases hassign with ⟨a, c, hplace, hheap, halive, hcompat, hpost⟩
      exact ⟨
        { value := _
          addr := a
          oldCell := c
          eval := hval
          place := hplace
          oldCellAt := hheap
          oldLive := halive
          valueCompat := hcompat
          postState := hpost }⟩

namespace AssignHeapWriteEffect

/-- Any address different from the written address has the same heap lookup. -/
theorem heap_other
    {σ σ' : State} {p : PlaceExpr} {e : ValExpr}
    (h : AssignHeapWriteEffect σ σ' p e) {b : Nat} :
    b ≠ h.addr → σ'.heap b = σ.heap b := by
  intro hb
  rw [h.postState]
  exact heap_writeHeap_other σ h.addr b { h.oldCell with value := some h.value } hb

end AssignHeapWriteEffect

/-- Existence of the object-declaration heap/cursor effect. -/
theorem nonempty_objectDeclHeapIntroEffect_of_declaresObject
    {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (h : DeclaresObject σ τ x ov σ') :
    Nonempty (ObjectDeclHeapIntroEffect σ σ' τ x ov) := by
  rcases h with ⟨aNext, hnext⟩
  rcases hnext with ⟨σcore, hpayload, hpolicy⟩
  exact ⟨
    { postCursor := aNext
      coreState := σcore
      payload := hpayload
      cursorPolicy := hpolicy }⟩

theorem nonempty_objectDeclHeapIntroEffect_of_none_step
    {σ σ' : State} {τ : CppType} {x : Ident} :
    BigStepStmt σ (.declareObj τ x none) .normal σ' →
    Nonempty (ObjectDeclHeapIntroEffect σ σ' τ x none) := by
  intro h
  cases h with
  | declareObjNone hdecl =>
      exact nonempty_objectDeclHeapIntroEffect_of_declaresObject hdecl

theorem exists_objectDeclHeapIntroEffect_of_some_step
    {σ σ' : State} {τ : CppType} {x : Ident} {e : ValExpr} :
    BigStepStmt σ (.declareObj τ x (some e)) .normal σ' →
    ∃ v, BigStepValue σ e v ∧
      Nonempty (ObjectDeclHeapIntroEffect σ σ' τ x (some v)) := by
  intro h
  cases h with
  | declareObjSome hval hdecl =>
      exact ⟨_, hval, nonempty_objectDeclHeapIntroEffect_of_declaresObject hdecl⟩

def refDeclBindingEffect_of_declaresRef
    {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat}
    (h : DeclaresRef σ τ x a σ') :
    RefDeclBindingEffect σ σ' τ x a := by
  rcases h with ⟨hfresh, c, hheap, hty, halive, hpost⟩
  exact
    { fresh := hfresh
      targetCell := ⟨c, hheap, hty, halive⟩
      postState := hpost }

theorem refDeclBindingEffect_of_step
    {σ σ' : State} {τ : CppType} {x : Ident} {p : PlaceExpr} :
    BigStepStmt σ (.declareRef τ x p) .normal σ' →
    ∃ a, BigStepPlace σ p a ∧ RefDeclBindingEffect σ σ' τ x a := by
  intro h
  cases h with
  | declareRef hplace hdecl =>
      exact ⟨_, hplace, refDeclBindingEffect_of_declaresRef hdecl⟩

end Cpp
