import CppFormalization.Cpp4.Resource.Demand.Place

/-!
# CppFormalization.Cpp4.Resource.Demand.Expr

Demand surfaces for value expressions.
-/

namespace Cpp4

/-- Resource demand required to evaluate a value expression. -/
structure ExprDemand where
  demands : DemandSet

namespace ExprDemand

def empty : ExprDemand where
  demands := []

def ofDemandSet (D : DemandSet) : ExprDemand where
  demands := D

/-- Literal expressions require no runtime resource. -/
def literal : ExprDemand :=
  empty

/-- Loading from a place inherits the place demand. -/
def load (p : PlaceDemand) : ExprDemand where
  demands := p.demands

/-- Taking an address inherits the place formation demand. -/
def addrOf (p : PlaceDemand) : ExprDemand where
  demands := p.demands

/-- Binary operators require both sub-expression demands. -/
def binary (lhs rhs : ExprDemand) : ExprDemand where
  demands := lhs.demands ++ rhs.demands

/-- Unary operators require the sub-expression demand. -/
def unary (e : ExprDemand) : ExprDemand where
  demands := e.demands

/-- Combine two expression-demand fragments. -/
def append (e₁ e₂ : ExprDemand) : ExprDemand where
  demands := e₁.demands ++ e₂.demands

end ExprDemand

end Cpp4
