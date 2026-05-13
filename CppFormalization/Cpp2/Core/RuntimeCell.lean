import CppFormalization.Cpp2.Core.RuntimeState

/-!
Primitive heap-cell observation predicates.
-/

namespace Cpp

def heapLiveTypedAt (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true

def heapInitializedTypedAt (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c v, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true ∧ c.value = some v ∧ ValueCompat v τ

/-- address `a` has a live `τ`-cell. -/
abbrev CellLiveTyped (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c, σ.heap a = some c ∧ c.ty = τ ∧ c.alive = true

/-- address `a` has a readable initialized `τ`-cell. -/
abbrev CellReadableTyped (σ : State) (a : Nat) (τ : CppType) : Prop :=
  ∃ c v,
    σ.heap a = some c ∧
    c.ty = τ ∧
    c.alive = true ∧
    c.value = some v ∧
    ValueCompat v τ

end Cpp
