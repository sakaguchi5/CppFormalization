import CppFormalization.Cpp2.Core.RuntimeState

/-!
Primitive runtime-state observation predicates.

These are vocabulary for talking about frames, bindings, ownership lists, and
heap cells.  They do not assert any invariant by themselves.
-/

namespace Cpp

def frameBindsObjectAddr (fr : ScopeFrame) (a : Nat) : Prop :=
  ∃ x τ, fr.binds x = some (.object τ a)

def runtimeFrameBindsObject (σ : State) (k : Nat) (x : Ident) (τ : CppType) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ fr.binds x = some (.object τ a)

def runtimeFrameBindsRef (σ : State) (k : Nat) (x : Ident) (τ : CppType) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ fr.binds x = some (.ref τ a)

def runtimeFrameOwnsAddress (σ : State) (k : Nat) (a : Nat) : Prop :=
  ∃ fr, σ.scopes[k]? = some fr ∧ a ∈ fr.locals

end Cpp
