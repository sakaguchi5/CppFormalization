import CppFormalization.Cpp4.Typing.Micro.EnvEffect
import CppFormalization.Cpp4.Resource.Demand.Expr

/-!
# CppFormalization.Cpp4.Typing.Micro.Place

Micro typing certificates for place expressions.

A place certificate carries the C++ place type and the resource demand needed to
form/use that place.  Dereference precision is intentionally staged: early
Judgment layers may supply a demand computed elsewhere, while later semantics can
replace that by value-sensitive dereference demand.
-/

namespace Cpp4

/-- How a typed place is going to be used. -/
inductive PlaceUse where
  | read
  | write
  | address
  deriving DecidableEq, Repr

/-- A typed place-expression certificate. -/
structure PlaceTyping (Γ : TypeEnv) (p : PlaceExpr) : Type where
  ty : CppType
  demand : PlaceDemand
  formation : Prop

namespace PlaceTyping

/-- A variable bound to an object is a place of that object type. -/
def varObject {Γ : TypeEnv} {x : Ident} {τ : CppType}
    (_bound : TypeEnv.Bound Γ x (.object τ)) :
    PlaceTyping Γ (.var x) where
  ty := τ
  demand := PlaceDemand.var x
  formation := TypeEnv.Bound Γ x (.object τ)

/-- A variable bound to a reference is a place of the referenced type. -/
def varRef {Γ : TypeEnv} {x : Ident} {τ : CppType}
    (_bound : TypeEnv.Bound Γ x (.ref τ)) :
    PlaceTyping Γ (.var x) where
  ty := τ
  demand := PlaceDemand.var x
  formation := TypeEnv.Bound Γ x (.ref τ)

/-- A dereference place from an already-computed pointer-expression demand.  The
initial Cpp4 micro layer keeps this value-insensitive; later layers can refine the
demand to concrete `canDerefRead` / `canDerefWrite` obligations. -/
def derefFromExprDemand {Γ : TypeEnv} {e : ValExpr} (τ : CppType)
    (ptrDemand : ExprDemand) : PlaceTyping Γ (.deref e) where
  ty := τ
  demand := PlaceDemand.ofDemandSet ptrDemand.demands
  formation := True

/-- Demand for reading this place.  The current structural layer reuses the
place-formation demand; later runtime-sensitive typing can refine it. -/
def readDemand {Γ : TypeEnv} {p : PlaceExpr} (h : PlaceTyping Γ p) : PlaceDemand :=
  h.demand

/-- Demand for writing this place. -/
def writeDemand {Γ : TypeEnv} {p : PlaceExpr} (h : PlaceTyping Γ p) : PlaceDemand :=
  h.demand

/-- Demand for taking this place's address. -/
def addressDemand {Γ : TypeEnv} {p : PlaceExpr} (h : PlaceTyping Γ p) : PlaceDemand :=
  h.demand

end PlaceTyping

end Cpp4
