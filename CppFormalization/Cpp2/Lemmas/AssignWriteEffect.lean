import CppFormalization.Cpp2.Semantics.Stmt

namespace Cpp

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

end Cpp
