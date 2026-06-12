import CppFormalization.Cpp4.Resource.Effect.Atom

/-!
# CppFormalization.Cpp4.Resource.Effect.Block

Effect composition for plan blocks.
-/

namespace Cpp4

namespace PlanBlockEffect

/-- Empty block effect. -/
def empty : PlanBlockEffect where
  effect := []

/-- The empty plan block produces no resource effect. -/
def nil : PlanBlockEffect :=
  empty

/-- Cons a head plan effect in front of a tail block effect. -/
def cons (head : PlanEffect) (tail : PlanBlockEffect) : PlanBlockEffect where
  effect := head.effect ++ tail.effect

/-- Append two block effect traces. -/
def append (left right : PlanBlockEffect) : PlanBlockEffect where
  effect := left.effect ++ right.effect

/-- Build a block effect from a list of plan effects. -/
def ofList : List PlanEffect → PlanBlockEffect
  | [] => nil
  | e :: es => cons e (ofList es)

end PlanBlockEffect

end Cpp4
