import CppFormalization.Cpp4.Resource.Demand.Core
import CppFormalization.Cpp4.Core.Syntax

/-!
# CppFormalization.Cpp4.Resource.Demand.Place

Demand surfaces for place expressions.  These are still intentionally light:
the static/typing layer will later compute richer demand sets from syntax.
-/

namespace Cpp4

/-- Resource demand required to use a place expression. -/
structure PlaceDemand where
  demands : DemandSet

namespace PlaceDemand

def empty : PlaceDemand where
  demands := []

def ofDemandSet (D : DemandSet) : PlaceDemand where
  demands := D

/-- A variable place needs its name to be bound. -/
def var (x : Ident) : PlaceDemand where
  demands := [.nameBound x]

/-- A concrete address used as a readable place. -/
def readableAddress (a : Address) (τ : CppType) : PlaceDemand where
  demands := [.canRead a τ]

/-- A concrete address used as a writable place. -/
def writableAddress (a : Address) (τ : CppType) : PlaceDemand where
  demands := [.canWrite a τ]

/-- A concrete pointer used as a readable dereference. -/
def derefRead (p : PtrValue) (τ : CppType) : PlaceDemand where
  demands := [.canDerefRead p τ]

/-- A concrete pointer used as a writable dereference. -/
def derefWrite (p : PtrValue) (τ : CppType) : PlaceDemand where
  demands := [.canDerefWrite p τ]

/-- Combine two place-demand fragments. -/
def append (p q : PlaceDemand) : PlaceDemand where
  demands := p.demands ++ q.demands

end PlaceDemand

end Cpp4
