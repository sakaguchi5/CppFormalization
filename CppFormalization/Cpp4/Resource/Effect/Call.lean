import CppFormalization.Cpp4.Resource.Effect.Core

/-!
# CppFormalization.Cpp4.Resource.Effect.Call

Call-oriented resource effect constructors.
-/

namespace Cpp4

namespace ResourceEffect

/-- Singleton trace for an internal call. -/
def callInternalTrace (f : FunctionName) : ResourceEffect :=
  [.callInternal f]

/-- Singleton trace for an external call. -/
def callExternalTrace (f : FunctionName) : ResourceEffect :=
  [.callExternal f]

end ResourceEffect

end Cpp4
