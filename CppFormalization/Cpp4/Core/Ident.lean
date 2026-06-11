import CppFormalization.Cpp4.Core.Keyword

/-!
# CppFormalization.Cpp4.Core.Ident

Identifier surfaces for user names and function names.
-/

namespace Cpp4

/-- Raw identifier spelling. Formation layers may require `ValidUserIdent`. -/
abbrev Ident := String

/-- Raw user identifier with a proof that it is lexically valid.
This is useful for formation layers, but raw syntax should usually use `Ident`. -/
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
