import CppFormalization.Cpp4.Resource.Demand.Block

/-!
# CppFormalization.Cpp4.Resource.Demand.Loop

Demand composition for `LoopPlan`.
-/

namespace Cpp4

namespace LoopDemand

/-- Empty loop demand. -/
def empty : LoopDemand where
  demands := []

/-- Build a loop demand from a raw demand set. -/
def ofDemandSet (D : DemandSet) : LoopDemand where
  demands := D

/-- Pre-test loop demand: evaluate the guard, then enter the body. -/
def preTest (cond : ExprDemand) (body : PlanDemand) : LoopDemand where
  demands := cond.demands ++ body.demands

/-- Post-test loop demand: enter the body, then evaluate the guard. -/
def postTest (body : PlanDemand) (cond : ExprDemand) : LoopDemand where
  demands := body.demands ++ cond.demands

/-- For-loop demand with already-computed fragments for initializer, optional
condition, iteration step, and body. -/
def forFrame
    (init : AtomDemand) (cond : Option ExprDemand)
    (iter : AtomDemand) (body : PlanDemand) : LoopDemand where
  demands :=
    init.demands ++
    (match cond with
     | none => []
     | some c => c.demands) ++
    body.demands ++ iter.demands

end LoopDemand

end Cpp4
