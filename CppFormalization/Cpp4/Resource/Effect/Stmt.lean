import CppFormalization.Cpp4.Resource.Effect.Call

/-!
# CppFormalization.Cpp4.Resource.Effect.Stmt

Statement-level resource effect surfaces.
-/

namespace Cpp4

namespace ResourceEffect

/-- Singleton trace for a write effect. -/
def writeObjectTrace (a : Address) (τ : CppType) : ResourceEffect :=
  [.writeObject a τ]

/-- Singleton trace for ending one object's lifetime. -/
def endLifetimeTrace (oid : ObjectId) : ResourceEffect :=
  [.endLifetime oid]

/-- Singleton trace for opening a scope. -/
def pushScopeTrace (sid : ScopeId) : ResourceEffect :=
  [.pushScope sid]

/-- Singleton trace for closing a scope. -/
def popScopeTrace (sid : ScopeId) : ResourceEffect :=
  [.popScope sid]

/-- Singleton trace for binding a name. -/
def bindNameTrace (sid : ScopeId) (x : Ident) (b : Binding) : ResourceEffect :=
  [.bindName sid x b]

end ResourceEffect

end Cpp4
