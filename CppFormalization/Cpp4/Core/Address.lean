import CppFormalization.Cpp4.Core.Type

/-!
# CppFormalization.Cpp4.Core.Address

Object identity and addresses.  Cpp4 keeps addresses first-class instead of
exposing raw `Nat` everywhere, so pointer/lifetime/resource transport can speak
about object identity directly.
-/

namespace Cpp4

/-- Stable identity of an allocated object/storage cell. -/
structure ObjectId where
  id : Nat
  deriving DecidableEq, Repr

/-- A minimal address: currently just an object identity.

Future extensions can add subobject paths, array elements, base-class paths, etc.
-/
structure Address where
  object : ObjectId
  deriving DecidableEq, Repr

namespace Address

/-- The root object reached by this address. -/
def rootObject (a : Address) : ObjectId :=
  a.object

end Address

end Cpp4
