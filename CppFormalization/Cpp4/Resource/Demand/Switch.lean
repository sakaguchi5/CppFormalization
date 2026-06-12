import CppFormalization.Cpp4.Resource.Demand.Loop

/-!
# CppFormalization.Cpp4.Resource.Demand.Switch

Demand composition for switch frames and selected switch suffixes.
-/

namespace Cpp4

/-- Resource demand required by one switch arm body. -/
structure SwitchArmDemand where
  demands : DemandSet

namespace SwitchArmDemand

/-- Build a switch-arm demand from its plan-block body demand. -/
def body (b : PlanBlockDemand) : SwitchArmDemand where
  demands := b.demands

end SwitchArmDemand

namespace SwitchDemand

/-- Empty switch demand. -/
def empty : SwitchDemand where
  demands := []

/-- A switch with no arms has no arm-body demand. -/
def nil : SwitchDemand :=
  empty

/-- Add an arm demand to a switch arm list demand. -/
def cons (arm : SwitchArmDemand) (rest : SwitchDemand) : SwitchDemand where
  demands := arm.demands ++ rest.demands

/-- Demand for a switch frame: evaluate the condition, then enter one of the
fallthrough suffixes.  Selection precision is intentionally supplied later; the
resource surface records the condition plus available suffix demand. -/
def frame (cond : ExprDemand) (suffix : SwitchDemand) : SwitchDemand where
  demands := cond.demands ++ suffix.demands

/-- Demand for an already-selected switch suffix. -/
def suffix (arms : SwitchDemand) : SwitchDemand :=
  arms

/-- Build a switch demand from arm demands. -/
def ofList : List SwitchArmDemand → SwitchDemand
  | [] => nil
  | a :: as => cons a (ofList as)

end SwitchDemand

end Cpp4
