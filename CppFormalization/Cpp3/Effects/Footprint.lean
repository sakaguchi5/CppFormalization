import CppFormalization.Cpp3.Core.All

/-!
# CppFormalization.Cpp3.Effects.Footprint

Small effect-footprint vocabulary for Cpp3.

This file intentionally contains only abstract sets and footprint packages.  It
is still below Boundary/Stability: it does not say that an access is safe, and it
does not prove that a later boundary is preserved.
-/

namespace Cpp3
namespace Effects

/-- A set of source-level names.  Static effects can usually see names before a
runtime address is known. -/
abbrev NameSet := Ident → Prop

/-- A set of runtime addresses.  Later Boundary/Stability layers may refine a
name footprint into an address footprint through lookup facts. -/
abbrev AddressSet := Nat → Prop

def emptyNameSet : NameSet :=
  fun _ => False

def singletonNameSet (x : Ident) : NameSet :=
  fun y => y = x

def unionNameSet (xs ys : NameSet) : NameSet :=
  fun x => xs x ∨ ys x

def subsetNameSet (xs ys : NameSet) : Prop :=
  ∀ x, xs x → ys x

def disjointNameSet (xs ys : NameSet) : Prop :=
  ∀ x, xs x → ys x → False

def emptyAddressSet : AddressSet :=
  fun _ => False

def singletonAddressSet (a : Nat) : AddressSet :=
  fun b => b = a

def unionAddressSet (xs ys : AddressSet) : AddressSet :=
  fun a => xs a ∨ ys a

def subsetAddressSet (xs ys : AddressSet) : Prop :=
  ∀ a, xs a → ys a

def disjointAddressSet (xs ys : AddressSet) : Prop :=
  ∀ a, xs a → ys a → False

/-- Name-level effect footprint.

The fields are deliberately separated so that later contracts can say precisely
which kind of non-interference is needed: read preservation, write separation,
no lifetime escape, or binding freshness. -/
structure NameFootprint : Type where
  reads : NameSet
  writes : NameSet
  binds : NameSet
  derefs : NameSet
  lifetimeEnds : NameSet

namespace NameFootprint

/-- Empty name footprint. -/
def empty : NameFootprint where
  reads := emptyNameSet
  writes := emptyNameSet
  binds := emptyNameSet
  derefs := emptyNameSet
  lifetimeEnds := emptyNameSet

/-- Pointwise union of name footprints. -/
def union (a b : NameFootprint) : NameFootprint where
  reads := unionNameSet a.reads b.reads
  writes := unionNameSet a.writes b.writes
  binds := unionNameSet a.binds b.binds
  derefs := unionNameSet a.derefs b.derefs
  lifetimeEnds := unionNameSet a.lifetimeEnds b.lifetimeEnds

end NameFootprint

/-- Address-level effect footprint.

This is mostly for later runtime Boundary/Stability layers.  The current Effects
layer can name it without deriving concrete addresses. -/
structure AddressFootprint : Type where
  reads : AddressSet
  writes : AddressSet
  derefs : AddressSet
  lifetimeEnds : AddressSet

namespace AddressFootprint

/-- Empty address footprint. -/
def empty : AddressFootprint where
  reads := emptyAddressSet
  writes := emptyAddressSet
  derefs := emptyAddressSet
  lifetimeEnds := emptyAddressSet

/-- Pointwise union of address footprints. -/
def union (a b : AddressFootprint) : AddressFootprint where
  reads := unionAddressSet a.reads b.reads
  writes := unionAddressSet a.writes b.writes
  derefs := unionAddressSet a.derefs b.derefs
  lifetimeEnds := unionAddressSet a.lifetimeEnds b.lifetimeEnds

end AddressFootprint

/-- Combined static/runtime footprint vocabulary. -/
structure Footprint : Type where
  names : NameFootprint
  addrs : AddressFootprint

namespace Footprint

/-- Empty combined footprint. -/
def empty : Footprint where
  names := NameFootprint.empty
  addrs := AddressFootprint.empty

/-- Pointwise union of combined footprints. -/
def union (a b : Footprint) : Footprint where
  names := NameFootprint.union a.names b.names
  addrs := AddressFootprint.union a.addrs b.addrs

end Footprint

end Effects
end Cpp3
