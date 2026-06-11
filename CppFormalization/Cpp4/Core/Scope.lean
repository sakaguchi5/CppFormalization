import CppFormalization.Cpp4.Core.Value

/-!
# CppFormalization.Cpp4.Core.Scope

Scope identity and runtime bindings.  `ScopeId` is first-class so block-open and
block-close transport can talk about the scope being preserved/closed instead of
only reasoning about list indices.
-/

namespace Cpp4

/-- Stable identity for a runtime scope frame. -/
structure ScopeId where
  id : Nat
  deriving DecidableEq, Repr

/-- Runtime binding payload. -/
inductive Binding where
  | object : CppType → Address → Binding
  | ref : CppType → Address → Binding
  deriving DecidableEq, Repr

def bindingType : Binding → CppType
  | .object τ _ => τ
  | .ref τ _ => τ

def bindingAddress : Binding → Address
  | .object _ a => a
  | .ref _ a => a

/-- Runtime scope frame.  `locals` records object ownership for scope close. -/
structure ScopeFrame where
  id : ScopeId
  binds : Ident → Option Binding
  locals : List ObjectId

/-- Empty scope frame with a chosen identity. -/
def emptyScopeFrame (sid : ScopeId) : ScopeFrame where
  id := sid
  binds := fun _ => none
  locals := []

end Cpp4
