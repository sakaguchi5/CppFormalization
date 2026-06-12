import CppFormalization.Cpp4.Resource.Demand.Switch

/-!
# CppFormalization.Cpp4.Resource.Demand.Plan

Demand composition for `ControlPlan`.
-/

namespace Cpp4

namespace PlanDemand

/-- Empty plan demand. -/
def empty : PlanDemand where
  demands := []

/-- Build a plan demand from a raw demand set. -/
def ofDemandSet (D : DemandSet) : PlanDemand where
  demands := D

/-- Atom plan demand. -/
def atom (a : AtomDemand) : PlanDemand where
  demands := a.demands

/-- Sequential demand: head demand followed by tail demand. -/
def seq (head tail : PlanDemand) : PlanDemand where
  demands := head.demands ++ tail.demands

/-- Branch demand: condition demand plus both branch surfaces.

This is a safe lower surface.  Later selected-route layers can refine this to
only the selected branch after condition evaluation. -/
def branch (cond : ExprDemand) (thenPlan elsePlan : PlanDemand) : PlanDemand where
  demands := cond.demands ++ thenPlan.demands ++ elsePlan.demands

/-- Scope-frame demand inherits the opened block demand. -/
def scopeFrame (b : PlanBlockDemand) : PlanDemand where
  demands := b.demands

/-- Loop-frame demand inherits the loop-plan demand. -/
def loopFrame (l : LoopDemand) : PlanDemand where
  demands := l.demands

/-- Switch-frame demand inherits the switch demand. -/
def switchFrame (s : SwitchDemand) : PlanDemand where
  demands := s.demands

/-- Selected switch suffix demand. -/
def switchSuffix (s : SwitchDemand) : PlanDemand where
  demands := s.demands

end PlanDemand

mutual
/-- Structural demand from ControlPlan syntax alone.

It follows the ControlPlan shape and handles control permissions for primitive
jumps, but leaves expression/place/call precision to later typed demand builders. -/
  def planDemandStructural : ControlPlan → PlanDemand
    | .atom a => PlanDemand.atom (AtomDemand.structural a)
    | .seq p q => PlanDemand.seq (planDemandStructural p) (planDemandStructural q)
    | .branch _ p q => PlanDemand.branch ExprDemand.empty (planDemandStructural p) (planDemandStructural q)
    | .scopeFrame b => PlanDemand.scopeFrame (planBlockDemandStructural b)
    | .loopFrame l => PlanDemand.loopFrame (loopDemandStructural l)
    | .switchFrame c arms => PlanDemand.switchFrame (switchDemandStructuralFrame c arms)
    | .switchSuffix arms => PlanDemand.switchSuffix (switchDemandStructuralSuffix arms)

  def planBlockDemandStructural : PlanBlock → PlanBlockDemand
    | .nil => PlanBlockDemand.nil
    | .cons p ps => PlanBlockDemand.cons (planDemandStructural p) (planBlockDemandStructural ps)

  def loopDemandStructural : LoopPlan → LoopDemand
    | .preTest _ body => { demands := (planDemandStructural body).demands }
    | .postTest body _ => { demands := (planDemandStructural body).demands }
    | .forFrame _ _ _ body => { demands := (planDemandStructural body).demands }

  def switchArmDemandStructural : SwitchPlanArm → SwitchArmDemand
    | .arm _ b => SwitchArmDemand.body (planBlockDemandStructural b)

  def switchDemandStructuralArms : SwitchPlanArmList → SwitchDemand
    | .nil => SwitchDemand.nil
    | .cons arm rest => SwitchDemand.cons (switchArmDemandStructural arm) (switchDemandStructuralArms rest)

  def switchDemandStructuralFrame (_cond : CppSwitchCond) (arms : SwitchPlanArmList) : SwitchDemand :=
    switchDemandStructuralArms arms

  def switchDemandStructuralSuffix (arms : SwitchPlanArmList) : SwitchDemand :=
    switchDemandStructuralArms arms
end

namespace PlanDemand

/-- Structural plan demand from syntax alone. -/
def structural : ControlPlan → PlanDemand :=
  planDemandStructural

end PlanDemand

namespace PlanBlockDemand

/-- Structural plan-block demand from syntax alone. -/
def structural : PlanBlock → PlanBlockDemand :=
  planBlockDemandStructural

end PlanBlockDemand

namespace LoopDemand

/-- Structural loop demand from syntax alone. -/
def structural : LoopPlan → LoopDemand :=
  loopDemandStructural

end LoopDemand

namespace SwitchArmDemand

/-- Structural switch-arm demand from syntax alone. -/
def structural : SwitchPlanArm → SwitchArmDemand :=
  switchArmDemandStructural

end SwitchArmDemand

namespace SwitchDemand

/-- Structural switch-arm-list demand. -/
def structuralArms : SwitchPlanArmList → SwitchDemand :=
  switchDemandStructuralArms

/-- Structural switch-frame demand from syntax alone. -/
def structuralFrame : CppSwitchCond → SwitchPlanArmList → SwitchDemand :=
  switchDemandStructuralFrame

/-- Structural selected-switch-suffix demand from syntax alone. -/
def structuralSuffix : SwitchPlanArmList → SwitchDemand :=
  switchDemandStructuralSuffix

end SwitchDemand

end Cpp4
