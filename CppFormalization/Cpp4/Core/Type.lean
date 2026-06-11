import CppFormalization.Cpp4.Core.Ident

/-!
# CppFormalization.Cpp4.Core.Type

Small C++ type vocabulary.  Function types are deliberately not object types;
function declarations live in `Core.Function`.
-/

namespace Cpp4

inductive BaseType where
  | void
  | bool
  | int
  deriving DecidableEq, Repr

inductive CppType where
  | base : BaseType → CppType
  | ptr  : CppType → CppType
  | ref  : CppType → CppType
  | array : CppType → Nat → CppType
  deriving DecidableEq, Repr

/-- Runtime object types supported by the initial executable fragment. -/
def ObjectType : CppType → Prop
  | .base .void => False
  | .ref _ => False
  | .array _ _ => False
  | _ => True

/-- Static declaration information stored in type environments. -/
inductive DeclInfo where
  | object : CppType → DeclInfo
  | ref : CppType → DeclInfo
  deriving DecidableEq, Repr

def declPlaceType : DeclInfo → CppType
  | .object τ => τ
  | .ref τ => τ

end Cpp4
