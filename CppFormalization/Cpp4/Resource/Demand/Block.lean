import CppFormalization.Cpp4.Resource.Demand.Atom

/-!
# CppFormalization.Cpp4.Resource.Demand.Block

Demand composition for `PlanBlock`.
-/

namespace Cpp4

namespace PlanBlockDemand

/-- Empty block demand. -/
def empty : PlanBlockDemand where
  demands := []

/-- The empty plan block requires no control-plan demand. -/
def nil : PlanBlockDemand :=
  empty

/-- Cons a head plan demand in front of a tail block demand. -/
def cons (head : PlanDemand) (tail : PlanBlockDemand) : PlanBlockDemand where
  demands := head.demands ++ tail.demands

/-- Append two plan-block demand fragments. -/
def append (left right : PlanBlockDemand) : PlanBlockDemand where
  demands := left.demands ++ right.demands

/-- Build a block demand from a list of plan demands. -/
def ofList : List PlanDemand → PlanBlockDemand
  | [] => nil
  | d :: ds => cons d (ofList ds)

end PlanBlockDemand

end Cpp4
