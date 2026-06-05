import CppFormalization.Cpp3.Core.RuntimeState

/-!
Primitive runtime freshness vocabulary.

Freshness here is only about the raw state: unused heap slot and absence from
all frame-local ownership lists.
-/

namespace Cpp3

def FreshAddressForState (σ : State) (a : Nat) : Prop :=
  σ.heap a = none ∧
  ∀ (k : Nat) (fr : ScopeFrame),
    σ.scopes[k]? = some fr →
    a ∉ fr.locals

/-- Freshness of an externally chosen post-state cursor. -/
abbrev FreshPostCursor (σ : State) (a : Nat) : Prop :=
  σ.heap a = none ∧
  ∀ (k : Nat) (fr : ScopeFrame),
    σ.scopes[k]? = some fr →
    a ∉ fr.locals

/-- The current runtime cursor is fresh against heap and owned locals. -/
abbrev nextFreshAgainstOwned (σ : State) : Prop :=
  σ.heap σ.next = none ∧
  ∀ (k : Nat) (fr : ScopeFrame),
    σ.scopes[k]? = some fr →
    σ.next ∉ fr.locals

end Cpp3
