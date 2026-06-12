import CppFormalization.Cpp4.Resource.Effect.Block

/-!
# CppFormalization.Cpp4.Resource.Effect.Loop

Effect composition for loop plans.
-/

namespace Cpp4

namespace LoopEffect

/-- Empty loop effect. -/
def empty : LoopEffect where
  effect := []

/-- Build a loop effect from a raw trace. -/
def ofEffect (eff : ResourceEffect) : LoopEffect where
  effect := eff

/-- Pre-test loop effect surface.  The precise number of iterations belongs to
semantics/divergence; this lower surface composes the one-step condition/body
fragments supplied by semantics. -/
def preTest (cond : ResourceEffect) (body : PlanEffect) : LoopEffect where
  effect := cond ++ body.effect

/-- Post-test loop effect surface. -/
def postTest (body : PlanEffect) (cond : ResourceEffect) : LoopEffect where
  effect := body.effect ++ cond

/-- For-loop effect surface. -/
def forFrame
    (init : AtomEffect) (cond : ResourceEffect)
    (iter : AtomEffect) (body : PlanEffect) : LoopEffect where
  effect := init.effect ++ cond ++ body.effect ++ iter.effect

end LoopEffect

end Cpp4
