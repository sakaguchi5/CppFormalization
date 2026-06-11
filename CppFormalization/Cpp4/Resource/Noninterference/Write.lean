import CppFormalization.Cpp4.Resource.Noninterference.Core

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Write

Atom-level noninterference for writes.
-/

namespace Cpp4

/-- Writing one object does not change heap lookup for a different object. -/
theorem heapAt_writeObject_unrelated
    {σ : State} {a b : Address} {τw : CppType} {v : Value}
    (h : b.object ≠ a.object) :
    heapAt (writeObjectState σ a τw v) b = heapAt σ b := by
  simp [heapAt, writeObjectState, h]

/-- A write to one object preserves read capability for an unrelated object. -/
theorem writeObject_preserves_unrelated_canRead
    {σ : State} {a b : Address} {τw τb : CppType} {v : Value}
    (h : b.object ≠ a.object) :
    CanRead σ b τb → CanRead (writeObjectState σ a τw v) b τb := by
  intro hread
  rcases hread with ⟨c, val, hheap, hlive, hty, hval, hcompat⟩
  refine ⟨c, val, ?_, hlive, hty, hval, hcompat⟩
  rw [heapAt_writeObject_unrelated (σ := σ) (a := a) (b := b) (τw := τw) (v := v) h]
  exact hheap

/-- A write to one object preserves write capability for an unrelated object. -/
theorem writeObject_preserves_unrelated_canWrite
    {σ : State} {a b : Address} {τw τb : CppType} {v : Value}
    (h : b.object ≠ a.object) :
    CanWrite σ b τb → CanWrite (writeObjectState σ a τw v) b τb := by
  intro hwrite
  rcases hwrite with ⟨c, hheap, hlive, hty⟩
  refine ⟨c, ?_, hlive, hty⟩
  rw [heapAt_writeObject_unrelated (σ := σ) (a := a) (b := b) (τw := τw) (v := v) h]
  exact hheap

end Cpp4
