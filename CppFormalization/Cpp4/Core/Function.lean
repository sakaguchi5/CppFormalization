import CppFormalization.Cpp4.Core.Type

/-!
# CppFormalization.Cpp4.Core.Function

Callable vocabulary that is intentionally independent from statement syntax.

The Resource layer only needs names, signatures, and callable declarations.  A
function body is a higher-level semantic object and must not be pulled into
resource capabilities, otherwise `Resource.Capability` depends on all of
`Core.Syntax`.
-/

namespace Cpp4

inductive ParamPassing where
  | byValue
  | byRef
  deriving DecidableEq, Repr

structure Param where
  name : Ident
  ty : CppType
  passing : ParamPassing
  validName : ValidUserIdent name

structure FunctionSig where
  params : List Param
  ret : CppType

/-- Whether a callable is implemented inside the Cpp fragment or supplied by an
external contract.  The actual internal body is deliberately not stored here. -/
inductive CallableKind where
  | internal
  | external
  deriving DecidableEq, Repr

/-- Callable declaration used by call typing and resource demand. -/
structure CallableDecl where
  sig : FunctionSig
  kind : CallableKind

/-- Function environment used by call demand and later call semantics. -/
structure FunctionEnv where
  lookup : FunctionName → Option CallableDecl

end Cpp4
