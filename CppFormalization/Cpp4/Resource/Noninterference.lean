import CppFormalization.Cpp4.Resource.Effect

/-!
# CppFormalization.Cpp4.Resource.Noninterference

Noninterference between an execution effect and future demands.

This file intentionally exposes the proof boundary.  Concrete effect/demand
analysis will later prove instances of `EffectPreservesDemand` for assignments,
declarations, calls, scope close, branch selection, and loop reentry.
-/

namespace Cpp4

/-- A resource effect preserves a future demand set across a concrete state
transition.  `D'` is explicit so declarations/calls/scope-close can transport the
future demand into a changed environment. -/
structure EffectPreservesDemand
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (D D' : DemandSet) : Type where
  preserved : DemandSetSatisfied χ σ D → DemandSetSatisfied χ' σ' D'

/-- A resource effect is known to invalidate a demand.  This is useful for
negative examples and for explaining why a program is outside the safe fragment. -/
structure EffectInvalidatesDemand
    (χ : DemandContext) (σ : State)
    (eff : ResourceEffect) (D : DemandSet) : Type where
  invalidated : Prop
  evidence : invalidated

end Cpp4
