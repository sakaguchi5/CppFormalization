import CppFormalization.Cpp4.Core.Function
import CppFormalization.Cpp4.Core.State

/-!
# CppFormalization.Cpp4.Resource.Capability

Primitive resource capabilities.  These are the atoms from which expression,
statement, block, and call demands are built.

This file intentionally depends only on state/storage and callable declarations.
It does not depend on statement syntax or function bodies.
-/

namespace Cpp4

/-- A runtime cell is live. -/
def CellLive (c : Cell) : Prop :=
  c.lifetime.status = .live

/-- Object address is allocated with a live cell. -/
def LiveObject (σ : State) (a : Address) : Prop :=
  ∃ c, heapAt σ a = some c ∧ CellLive c

/-- Address can be read as a value of type `τ`. -/
def CanRead (σ : State) (a : Address) (τ : CppType) : Prop :=
  ∃ c v, heapAt σ a = some c ∧
    CellLive c ∧ c.ty = τ ∧ c.value = some v ∧ ValueCompat v τ

/-- Address can be written as a value of type `τ`. -/
def CanWrite (σ : State) (a : Address) (τ : CppType) : Prop :=
  ∃ c, heapAt σ a = some c ∧ CellLive c ∧ c.ty = τ

/-- Pointer can be dereferenced for read.  Null pointer is explicitly not readable. -/
def CanDerefRead (σ : State) (p : PtrValue) (τ : CppType) : Prop :=
  match p with
  | .null => False
  | .addr a => CanRead σ a τ

/-- Pointer can be dereferenced for write.  Null pointer is explicitly not writable. -/
def CanDerefWrite (σ : State) (p : PtrValue) (τ : CppType) : Prop :=
  match p with
  | .null => False
  | .addr a => CanWrite σ a τ

/-- A function name resolves in a function environment. -/
def CallableResolved (fnEnv : FunctionEnv) (f : FunctionName) : Prop :=
  ∃ c, fnEnv.lookup f = some c

end Cpp4
