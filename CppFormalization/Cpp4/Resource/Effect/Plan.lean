import CppFormalization.Cpp4.Resource.Effect.Switch

/-!
# CppFormalization.Cpp4.Resource.Effect.Plan

Effect composition for `ControlPlan`.
-/

namespace Cpp4

namespace PlanEffect

/-- Empty plan effect. -/
def empty : PlanEffect where
  effect := []

/-- Build a plan effect from a raw trace. -/
def ofEffect (eff : ResourceEffect) : PlanEffect where
  effect := eff

/-- Atom plan effect. -/
def atom (a : AtomEffect) : PlanEffect where
  effect := a.effect

/-- Sequential plan effect composition. -/
def seq (head tail : PlanEffect) : PlanEffect where
  effect := head.effect ++ tail.effect

/-- Branch effect surface.  Selected-route semantics can later refine this to the
chosen branch; this lower surface records the available branch fragments. -/
def branch (cond : ResourceEffect) (thenPlan elsePlan : PlanEffect) : PlanEffect where
  effect := cond ++ thenPlan.effect ++ elsePlan.effect

/-- Scope-frame effect: push/open/close effects are supplied by semantics; this
constructor records the body fragment. -/
def scopeFrame (body : PlanBlockEffect) : PlanEffect where
  effect := body.effect

/-- Loop-frame effect. -/
def loopFrame (l : LoopEffect) : PlanEffect where
  effect := l.effect

/-- Switch-frame effect. -/
def switchFrame (s : SwitchEffect) : PlanEffect where
  effect := s.effect

/-- Selected switch suffix effect. -/
def switchSuffix (s : SwitchEffect) : PlanEffect where
  effect := s.effect

end PlanEffect

mutual
/-- Structural effect from ControlPlan syntax alone. -/
  def planEffectStructural : ControlPlan → PlanEffect
    | .atom a => PlanEffect.atom (AtomEffect.structural a)
    | .seq p q => PlanEffect.seq (planEffectStructural p) (planEffectStructural q)
    | .branch _ p q => PlanEffect.branch [] (planEffectStructural p) (planEffectStructural q)
    | .scopeFrame b => PlanEffect.scopeFrame (planBlockEffectStructural b)
    | .loopFrame l => PlanEffect.loopFrame (loopEffectStructural l)
    | .switchFrame c arms => PlanEffect.switchFrame (switchEffectStructuralFrame c arms)
    | .switchSuffix arms => PlanEffect.switchSuffix (switchEffectStructuralSuffix arms)

  def planBlockEffectStructural : PlanBlock → PlanBlockEffect
    | .nil => PlanBlockEffect.nil
    | .cons p ps => PlanBlockEffect.cons (planEffectStructural p) (planBlockEffectStructural ps)

  def loopEffectStructural : LoopPlan → LoopEffect
    | .preTest _ body => { effect := (planEffectStructural body).effect }
    | .postTest body _ => { effect := (planEffectStructural body).effect }
    | .forFrame _ _ _ body => { effect := (planEffectStructural body).effect }

  def switchArmEffectStructural : SwitchPlanArm → SwitchArmEffect
    | .arm _ b => SwitchArmEffect.body (planBlockEffectStructural b)

  def switchEffectStructuralArms : SwitchPlanArmList → SwitchEffect
    | .nil => SwitchEffect.nil
    | .cons arm rest => SwitchEffect.cons (switchArmEffectStructural arm) (switchEffectStructuralArms rest)

  def switchEffectStructuralFrame (_cond : CppSwitchCond) (arms : SwitchPlanArmList) : SwitchEffect :=
    switchEffectStructuralArms arms

  def switchEffectStructuralSuffix (arms : SwitchPlanArmList) : SwitchEffect :=
    switchEffectStructuralArms arms
end

namespace PlanEffect

/-- Structural plan effect from syntax alone. -/
def structural : ControlPlan → PlanEffect :=
  planEffectStructural

end PlanEffect

namespace PlanBlockEffect

/-- Structural plan-block effect from syntax alone. -/
def structural : PlanBlock → PlanBlockEffect :=
  planBlockEffectStructural

end PlanBlockEffect

namespace LoopEffect

/-- Structural loop effect from syntax alone. -/
def structural : LoopPlan → LoopEffect :=
  loopEffectStructural

end LoopEffect

namespace SwitchArmEffect

/-- Structural switch-arm effect from syntax alone. -/
def structural : SwitchPlanArm → SwitchArmEffect :=
  switchArmEffectStructural

end SwitchArmEffect

namespace SwitchEffect

/-- Structural switch-arm-list effect. -/
def structuralArms : SwitchPlanArmList → SwitchEffect :=
  switchEffectStructuralArms

/-- Structural switch-frame effect from syntax alone. -/
def structuralFrame : CppSwitchCond → SwitchPlanArmList → SwitchEffect :=
  switchEffectStructuralFrame

/-- Structural selected-switch-suffix effect from syntax alone. -/
def structuralSuffix : SwitchPlanArmList → SwitchEffect :=
  switchEffectStructuralSuffix

end SwitchEffect

end Cpp4
