import CppFormalization.Cpp2.Semantics.Stmt
import CppFormalization.Cpp2.Static.ScopeDiscipline
import CppFormalization.Cpp2.Static.Assumptions
/-!
Bridge lemmas from concrete semantics into safety predicates.
-/

namespace Cpp

/-!  Safety bridge lemmas. -/

@[simp] theorem readablePlace_implies_valid
    {σ : State} {p : PlaceExpr} :
    ReadablePlace σ p → ValidPlace σ p := by
  intro h
  rcases h with ⟨a, c, v, hp, hh, halive, _⟩
  exact ⟨a, c, hp, hh, halive⟩


@[simp] theorem bigStepValue_load_readable
    {σ : State} {p : PlaceExpr} {v : Value} :
    BigStepValue σ (.load p) v → ReadablePlace σ p := by
  intro h
  cases h with
  | load hp hh halive hval =>
      exact ⟨_, _, _, hp, hh, halive, hval⟩

@[simp] theorem assigns_place
    {σ σ' : State} {p : PlaceExpr} {v : Value} :
    Assigns σ p v σ' → ∃ a c,
      BigStepPlace σ p a ∧
      σ.heap a = some c ∧
      c.alive = true ∧
      ValueCompat v c.ty ∧
      σ' = writeHeap σ a { c with value := some v } := by
  intro h
  exact h

@[simp] theorem declaresObject_eq_setNext_core
    {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    DeclaresObject σ τ x ov σ' →
    ∃ aNext, σ' = setNext (declareObjectStateCore σ τ x ov) aNext := by
  intro h
  rcases h with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨_, _, _, _, hcore⟩
  rcases hpolicy with ⟨_, hσ'⟩
  subst hcore
  exact ⟨aNext, hσ'⟩

@[simp] theorem declaresRef_eq
    {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    DeclaresRef σ τ x a σ' →
    σ' = declareRefState σ τ x a := by
  intro h
  rcases h.2 with ⟨c, _, _, _, hσ'⟩
  exact hσ'

@[simp] theorem breakWellScopedAt_zero_breakStmt :
    ¬ BreakWellScopedAt 0 .breakStmt := by
  simp [BreakWellScopedAt]

@[simp] theorem breakWellScopedAt_succ_breakStmt (d : Nat) :
    BreakWellScopedAt (Nat.succ d) .breakStmt := by
  simp [BreakWellScopedAt]

end Cpp
