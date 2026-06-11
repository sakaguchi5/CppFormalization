import CppFormalization.Cpp4.Resource.Effect.All

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Core

Core noninterference vocabulary: an effect preserves a future demand set across a
state transition.
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

/-- Object mentioned by a primitive demand, if any. -/
def DemandMentionsObject (oid : ObjectId) : ResourceDemand → Prop
  | .liveObject a => a.object = oid
  | .canRead a _ => a.object = oid
  | .canWrite a _ => a.object = oid
  | .canDerefRead (.addr a) _ => a.object = oid
  | .canDerefWrite (.addr a) _ => a.object = oid
  | _ => False

/-- A primitive demand is unrelated to an object lifetime/write target. -/
def DemandUnrelatedObject (oid : ObjectId) (d : ResourceDemand) : Prop :=
  ¬ DemandMentionsObject oid d

/-- A packaged preservation certificate for one primitive demand. -/
structure PreservesPrimitiveDemand
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (d d' : ResourceDemand) : Type where
  preserved : DemandSatisfied χ σ d → DemandSatisfied χ' σ' d'

/-- Lift primitive preservation pointwise to singleton demand sets. -/
def preserves_singleton
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {d d' : ResourceDemand}
    (h : PreservesPrimitiveDemand χ χ' σ σ' eff d d') :
    EffectPreservesDemand χ χ' σ σ' eff [d] [d'] := by
  constructor
  intro hD
  intro q hq
  cases hq with
  | head =>
      exact h.preserved (hD d (by simp))
  | tail _ htail => cases htail

end Cpp4
