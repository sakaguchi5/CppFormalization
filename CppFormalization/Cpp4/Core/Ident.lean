import CppFormalization.Cpp4.Core.Keyword

/-!
# CppFormalization.Cpp4.Core.Ident

Identifier surfaces for user names and function names.

The Core AST uses raw `Ident` values.  A later Source/Static layer may require
`UserIdent` when it wants to state the lexical fact that a spelling is not a
reserved keyword.
-/

namespace Cpp4

/-- Raw identifier spelling. Formation layers may require `ValidUserIdent`. -/
abbrev Ident := String

/-- Raw user identifier with a proof that it is lexically valid.
This is useful for formation layers, but Core syntax usually stays proof-free. -/
structure UserIdent where
  name : Ident
  valid : ValidUserIdent name

/-- Raw function-name spelling.
Validity and callability are checked by formation / typing / resource layers. -/
structure FunctionName where
  name : Ident
  deriving DecidableEq, Repr

namespace UserIdent

instance : Coe UserIdent Ident where
  coe x := x.name

end UserIdent

namespace FunctionName

instance : Coe FunctionName Ident where
  coe f := f.name

def valid (f : FunctionName) : Prop :=
  ValidUserIdent f.name

end FunctionName

end Cpp4
