import CppFormalization.Cpp3.SafetyFragment.All

/-!
# CppFormalization.Cpp3.Boundary.Core

Runtime boundary vocabulary.

The `Boundary` layer is the first layer in the Cpp3 safety stack that mentions a
concrete runtime `State`.  It does not prove progress, preservation, or stability.
It only packages the runtime facts needed to enter an expression, statement,
block, or selected continuation point.
-/

namespace Cpp3
namespace Boundary

/-- A source name resolves to a runtime binding in the current state. -/
structure RuntimeNameResolved (σ : State) (x : Ident) : Type where
  binding : Binding
  lookup : lookupBinding σ x = some binding

/-- A source name resolves to an object binding. -/
structure RuntimeObjectResolved (σ : State) (x : Ident) (τ : CppType) (addr : Nat) : Type where
  lookup : lookupBinding σ x = some (.object τ addr)

/-- A source name resolves to a reference binding. -/
structure RuntimeRefResolved (σ : State) (x : Ident) (τ : CppType) (addr : Nat) : Type where
  lookup : lookupBinding σ x = some (.ref τ addr)

/-- A heap cell exists at a runtime address. -/
structure RuntimeCellAt (σ : State) (addr : Nat) : Type where
  cell : Cell
  lookup : σ.heap addr = some cell

/-- A runtime address contains a live cell. -/
structure RuntimeLiveCell (σ : State) (addr : Nat) : Type where
  cell : Cell
  lookup : σ.heap addr = some cell
  alive : cell.alive = true

/-- A runtime address contains a cell with the expected type. -/
structure RuntimeTypedCell (σ : State) (addr : Nat) (τ : CppType) : Type where
  cell : Cell
  lookup : σ.heap addr = some cell
  typeEq : cell.ty = τ

/-- A runtime address is readable as a typed value. -/
structure RuntimeReadableCell
    (σ : State) (addr : Nat) (τ : CppType) (v : Value) : Type where
  cell : Cell
  lookup : σ.heap addr = some cell
  alive : cell.alive = true
  typeEq : cell.ty = τ
  stored : cell.value = some v
  compat : ValueCompat v τ

/-- A runtime address is writable at the expected type. -/
structure RuntimeWritableCell (σ : State) (addr : Nat) (τ : CppType) : Type where
  cell : Cell
  lookup : σ.heap addr = some cell
  alive : cell.alive = true
  typeEq : cell.ty = τ

/-- The current runtime cursor can be used as fresh storage for a declaration. -/
structure RuntimeCurrentCursorFresh (σ : State) : Type where
  fresh : nextFreshAgainstOwned σ

/-- The current runtime scope can accept a new declaration name. -/
structure RuntimeCurrentScopeFreshName (σ : State) (x : Ident) : Type where
  fresh : currentScopeFresh σ x

/-- Generic explicit boundary evidence.

The proposition is an argument rather than a hidden field, so a runtime boundary
evidence package is visibly evidence for a particular boundary obligation `P`. -/
structure RuntimeBoundaryEvidence
    (kind : Contracts.ObligationFamily) (P : Prop) : Type where
  evidence : Contracts.Requires P

namespace RuntimeBoundaryEvidence

/-- Extract the proposition carried by a runtime boundary evidence package. -/
def get {kind : Contracts.ObligationFamily} {P : Prop}
    (h : RuntimeBoundaryEvidence kind P) : P :=
  h.evidence

end RuntimeBoundaryEvidence

/-- Marker for the adopted boundary policy. -/
def boundaryLayerPolicy : String :=
  "Boundary packages concrete state-entry facts; Stability and Soundness remain later layers."

end Boundary
end Cpp3
