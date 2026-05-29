universe u

/-!
Foundational type vocabulary.
This file carries only the smallest static objects and their immediate relations.
-/

namespace Cpp

abbrev Ident := String

inductive BaseType where
  | void
  | bool
  | int
  deriving DecidableEq, Repr

inductive CppType where
  | base  : BaseType → CppType
  | ptr   : CppType → CppType
  | ref   : CppType → CppType
  | array : CppType → Nat → CppType
  deriving DecidableEq, Repr

/-- Object declarations supported by the current runtime core.
    Arrays and `void` are intentionally left outside this executable fragment. -/
def ObjectType : CppType → Prop
  | .base .void => False
  | .ref _ => False
  | .array _ _ => False
  | _ => True

inductive Value where
  | unit
  | bool : Bool → Value
  | int  : Int → Value
  | addr : Nat → Value
  deriving DecidableEq, Repr

inductive DeclInfo where
  | object : CppType → DeclInfo
  | ref    : CppType → DeclInfo
  deriving DecidableEq, Repr

def declPlaceType : DeclInfo → CppType
  | .object τ => τ
  | .ref τ => τ

inductive ValueCompat : Value → CppType → Prop where
  | unit : ValueCompat .unit (.base .void)
  | bool {b : Bool} : ValueCompat (.bool b) (.base .bool)
  | int  {n : Int}  : ValueCompat (.int n) (.base .int)
  | ptr  {a : Nat} {τ : CppType} : ValueCompat (.addr a) (.ptr τ)

end Cpp
