import CppFormalization.Cpp4.Core.Address

/-!
# CppFormalization.Cpp4.Core.Value

Runtime values.  Null pointer is included from the beginning because pointer
resource demands must distinguish null from live dereferenceable addresses.
-/

namespace Cpp4

/-- Pointer values in the initial Cpp4 fragment. -/
inductive PtrValue where
  | null
  | addr : Address → PtrValue
  deriving DecidableEq, Repr

inductive Value where
  | unit
  | bool : Bool → Value
  | int : Int → Value
  | ptr : PtrValue → Value
  deriving DecidableEq, Repr

/-- Value/type compatibility.  `nullptr` is compatible with every pointer type,
but it is not dereferenceable; dereferenceability is a resource capability. -/
inductive ValueCompat : Value → CppType → Prop where
  | unit : ValueCompat .unit (.base .void)
  | bool {b : Bool} : ValueCompat (.bool b) (.base .bool)
  | int {n : Int} : ValueCompat (.int n) (.base .int)
  | ptrNull {τ : CppType} : ValueCompat (.ptr .null) (.ptr τ)
  | ptrAddr {a : Address} {τ : CppType} : ValueCompat (.ptr (.addr a)) (.ptr τ)

end Cpp4
