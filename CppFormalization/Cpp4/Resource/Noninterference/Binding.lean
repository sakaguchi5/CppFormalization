import CppFormalization.Cpp4.Resource.Noninterference.Scope

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Binding

Atom-level noninterference for name binding.
-/

namespace Cpp4

/-- Binding a name in the top frame preserves lookup for unrelated names. -/
theorem lookupBinding_bindName_unrelated
    {σ : State} {x y : Ident} {b : Binding}
    (h : y ≠ x) :
    lookupBinding (bindNameState σ x b) y = lookupBinding σ y := by
  cases σ with
  | mk scopes heap nextObject nextScope =>
      cases scopes with
      | nil => simp [bindNameState]
      | cons fr rest =>
          simp [bindNameState, lookupBinding, lookupBindingFrames, h]

/-- Binding a name preserves an unrelated `nameBound` demand. -/
theorem bindName_preserves_unrelated_name
    {χ : DemandContext} {σ : State} {x y : Ident} {bnd : Binding}
    (h : y ≠ x) :
    DemandSatisfied χ σ (.nameBound y) →
      DemandSatisfied χ (bindNameState σ x bnd) (.nameBound y) := by
  intro hsat
  rcases hsat with ⟨old, hold⟩
  exact ⟨old, by
    rw [lookupBinding_bindName_unrelated (σ := σ) (x := x) (y := y) (b := bnd) h]
    exact hold⟩

end Cpp4
