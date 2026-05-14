import CppFormalization.Cpp2.Semantics.Stmt
import CppFormalization.Cpp2.Core.RuntimeOps
import CppFormalization.Cpp2.Static.Pure.ReplayStableReadPlace
import CppFormalization.Cpp2.Semantics.Facts.ExprDeterminism

namespace Cpp

/-!
# CppFormalization.Cpp2.Semantics.Facts.AssignWrite

Assignment write-effect and write-footprint facts derived from Assigns/BigStepStmt.
-/


/-!
# Lemmas.AssignWriteEffect

The pure write-effect boundary exposed by an assignment step.

This is kept below Closure/Internal because it is theorem-backed directly from
`Assigns` and does not contain any readiness/replay transport axiom.
-/

/-- Logical write-effect boundary exposed by an assignment step. -/
def AssignWriteEffect
    (σ σ' : State) (p : PlaceExpr) (v : Value) : Prop :=
  ∃ a c,
    BigStepPlace σ p a ∧
    σ.heap a = some c ∧
    c.alive = true ∧
    σ' = writeHeap σ a { c with value := some v }

/-- `Assigns` already packages the operational data needed for the logical write effect. -/
theorem assignWriteEffect_of_Assigns
    {σ σ' : State} {p : PlaceExpr} {v : Value} :
    Assigns σ p v σ' →
    AssignWriteEffect σ σ' p v := by
  intro hassign
  rcases hassign with ⟨a, c, hplace, hheap, halive, _hcompat, rfl⟩
  exact ⟨a, c, hplace, hheap, halive, rfl⟩

@[simp] theorem writeHeap_heap_eq
    {σ : State} {a : Nat} {c : Cell} :
    (writeHeap σ a c).heap a = some c := by
  simp [writeHeap]

@[simp] theorem writeHeap_heap_ne
    {σ : State} {a b : Nat} {c : Cell}
    (h : b ≠ a) :
    (writeHeap σ a c).heap b = σ.heap b := by
  simp [writeHeap, h]

@[simp] theorem writeHeap_scopes
    {σ : State} {a : Nat} {c : Cell} :
    (writeHeap σ a c).scopes = σ.scopes := by
  rfl

@[simp] theorem writeHeap_next
    {σ : State} {a : Nat} {c : Cell} :
    (writeHeap σ a c).next = σ.next := by
  rfl

theorem bigStepPlace_replayStableReadPlace_after_writeHeap
    {σ : State} {aW a : Nat} {cW : Cell}
    {p : PlaceExpr} :
    ReplayStableReadPlace p →
    BigStepPlace σ p a →
    BigStepPlace (writeHeap σ aW cW) p a := by
  intro hpstable hplace
  cases hpstable with
  | var =>
      cases hplace with
      | varObject hbind =>
          exact BigStepPlace.varObject (by simpa using hbind)
      | varRef hbind =>
          exact BigStepPlace.varRef (by simpa using hbind)

theorem bigStepPlace_replayStableReadPlace_after_assign
    {σ σ' : State} {q : PlaceExpr} {rhs : ValExpr}
    {p : PlaceExpr} {a : Nat} :
    ReplayStableReadPlace p →
    BigStepPlace σ p a →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BigStepPlace σ' p a := by
  intro hpstable hplace hstep
  cases hstep with
  | assign hval hassign =>
      rcases hassign with ⟨aW, cW, hwrite, hheap, halive, hcompat, rfl⟩
      exact bigStepPlace_replayStableReadPlace_after_writeHeap hpstable hplace

theorem assigns_heap_unchanged_off_target
    {σ σ' : State} {q : PlaceExpr} {v : Value}
    {aW a : Nat} {c : Cell} :
    BigStepPlace σ q aW →
    a ≠ aW →
    σ.heap a = some c →
    Assigns σ q v σ' →
    σ'.heap a = some c := by
  intro hwrite hneq hheap hassign
  rcases hassign with ⟨aW', cW, hwrite', hheapW, halive, hcompat, rfl⟩
  have hEq : aW' = aW := by
    exact bigStepPlace_deterministic hwrite' hwrite
  subst hEq
  simp [writeHeap, hneq, hheap]

theorem bigStepStmt_assign_heap_unchanged_off_target
    {σ σ' : State} {q : PlaceExpr} {rhs : ValExpr}
    {aW a : Nat} {c : Cell} :
    BigStepPlace σ q aW →
    a ≠ aW →
    σ.heap a = some c →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    σ'.heap a = some c := by
  intro hwrite hneq hheap hstep
  cases hstep with
  | assign hval hassign =>
      exact assigns_heap_unchanged_off_target hwrite hneq hheap hassign

end Cpp
