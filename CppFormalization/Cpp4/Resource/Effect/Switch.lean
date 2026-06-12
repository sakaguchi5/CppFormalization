import CppFormalization.Cpp4.Resource.Effect.Loop

/-!
# CppFormalization.Cpp4.Resource.Effect.Switch

Effect composition for switch frames and selected suffixes.
-/

namespace Cpp4

/-- Resource effect produced by one switch arm body. -/
structure SwitchArmEffect where
  effect : ResourceEffect

namespace SwitchArmEffect

/-- Build a switch-arm effect from its body block effect. -/
def body (b : PlanBlockEffect) : SwitchArmEffect where
  effect := b.effect

end SwitchArmEffect

namespace SwitchEffect

/-- Empty switch effect. -/
def empty : SwitchEffect where
  effect := []

/-- No switch arms produce no arm-body effect. -/
def nil : SwitchEffect :=
  empty

/-- Add one arm effect to a switch arm-list effect. -/
def cons (arm : SwitchArmEffect) (rest : SwitchEffect) : SwitchEffect where
  effect := arm.effect ++ rest.effect

/-- Switch frame effect: condition effect followed by the selected suffix effect.
Selection precision is supplied later by semantics. -/
def frame (cond : ResourceEffect) (suffix : SwitchEffect) : SwitchEffect where
  effect := cond ++ suffix.effect

/-- Already-selected switch suffix effect. -/
def suffix (arms : SwitchEffect) : SwitchEffect :=
  arms

/-- Build a switch effect from arm effects. -/
def ofList : List SwitchArmEffect → SwitchEffect
  | [] => nil
  | a :: as => cons a (ofList as)

end SwitchEffect

end Cpp4
