import CppFormalization.Cpp4.Resource.Noninterference.Write

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Lifetime

Atom-level noninterference and invalidation for lifetime ending.
-/

namespace Cpp4

/-- Ending one lifetime does not change heap lookup for a different object. -/
theorem heapAt_endLifetime_unrelated
    {σ : State} {oid : ObjectId} {a : Address}
    (h : a.object ≠ oid) :
    heapAt (endLifetimeState σ oid) a = heapAt σ a := by
  simp [heapAt, endLifetimeState, h]

/-- Ending the lifetime of an object invalidates read capability for that object. -/
theorem endLifetime_invalidates_same_object_canRead
    {σ : State} {a : Address} {τ : CppType} :
    ¬ CanRead (endLifetimeState σ a.object) a τ := by
  intro hread
  rcases hread with ⟨c, v, hheap, hlive, hty, hval, hcompat⟩
  unfold heapAt endLifetimeState at hheap
  cases hcell : σ.heap a.object with
  | none =>
      simp [hcell] at hheap
  | some c₀ =>
      simp [hcell] at hheap
      subst c
      unfold CellLive at hlive
      simp [endLifetimeCell] at hlive

/-- Ending one object preserves read capability for an unrelated object. -/
theorem endLifetime_preserves_unrelated_canRead
    {σ : State} {oid : ObjectId} {a : Address} {τ : CppType}
    (h : a.object ≠ oid) :
    CanRead σ a τ → CanRead (endLifetimeState σ oid) a τ := by
  intro hread
  rcases hread with ⟨c, v, hheap, hlive, hty, hval, hcompat⟩
  refine ⟨c, v, ?_, hlive, hty, hval, hcompat⟩
  rw [heapAt_endLifetime_unrelated (σ := σ) (oid := oid) (a := a) h]
  exact hheap

/-- Ending one object preserves write capability for an unrelated object. -/
theorem endLifetime_preserves_unrelated_canWrite
    {σ : State} {oid : ObjectId} {a : Address} {τ : CppType}
    (h : a.object ≠ oid) :
    CanWrite σ a τ → CanWrite (endLifetimeState σ oid) a τ := by
  intro hwrite
  rcases hwrite with ⟨c, hheap, hlive, hty⟩
  refine ⟨c, ?_, hlive, hty⟩
  rw [heapAt_endLifetime_unrelated (σ := σ) (oid := oid) (a := a) h]
  exact hheap

/-- Generic primitive-demand preservation for lifetime end, packaged as the exact
obligation that later demand analyzers should discharge. -/
structure EndLifetimeUnrelatedDemand
    (χ : DemandContext) (σ : State) (oid : ObjectId) (d : ResourceDemand) : Type where
  unrelated : DemandUnrelatedObject oid d
  preserved : DemandSatisfied χ σ d → DemandSatisfied χ (endLifetimeState σ oid) d

/-- Lifetime end preserves a demand once the demand analyzer proves it is unrelated. -/
theorem endLifetime_preserves_unrelated_demand
    {χ : DemandContext} {σ : State} {oid : ObjectId} {d : ResourceDemand}
    (h : EndLifetimeUnrelatedDemand χ σ oid d) :
    DemandSatisfied χ σ d → DemandSatisfied χ (endLifetimeState σ oid) d :=
  h.preserved

end Cpp4
