import CppFormalization.Cpp4.Resource.Certification.Provider

/-!
# CppFormalization.Cpp4.Resource.Certification.Abstract

Abstract names for the resource-certification pipeline.

This file does not prove A/B/C1.  It only makes the role of the current
`GeneratedDemand` / `GeneratedEffect` containers explicit: they are machine
footprints, while adequacy is supplied later from `Typing` and `Semantics`.
-/

namespace Cpp4

universe u v

/-- A machine-computed future-demand footprint for a target.

This is definitionally the current `GeneratedDemand`; the name emphasizes that
adequacy is not stored here. -/
abbrev DemandFootprint {α : Type u} (target : α) : Type u :=
  GeneratedDemand target

/-- A machine-recorded resource-effect footprint for a state transition.

This is definitionally the current `GeneratedEffect`; the name emphasizes that
semantics adequacy is supplied above the resource layer. -/
abbrev EffectFootprint (σ σ' : State) : Type :=
  GeneratedEffect σ σ'

/-- The demand-footprint pair that C2 will eventually transport across an effect. -/
structure DemandFootprintPair
    {α : Type u} {β : Type v} (beforeTarget : α) (afterTarget : β) : Type (max u v) where
  before : DemandFootprint beforeTarget
  after : DemandFootprint afterTarget

namespace DemandFootprintPair

/-- Before-demand set carried by a demand-footprint pair. -/
def beforeDemands
    {α : Type u} {β : Type v} {beforeTarget : α} {afterTarget : β}
    (h : DemandFootprintPair beforeTarget afterTarget) : DemandSet :=
  h.before.demands

/-- After-demand set carried by a demand-footprint pair. -/
def afterDemands
    {α : Type u} {β : Type v} {beforeTarget : α} {afterTarget : β}
    (h : DemandFootprintPair beforeTarget afterTarget) : DemandSet :=
  h.after.demands

end DemandFootprintPair

/-- Build the current pipeline from named footprints and noninterference.

This is the common endpoint for A/B/C1 before Boundary.Transport performs C2. -/
def ResourceCertificationPipeline.ofFootprints
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (demands : DemandFootprintPair beforeTarget afterTarget)
    (effect : EffectFootprint σ σ')
    (hNI : NoninterferenceCertificate χ χ' σ σ'
      effect.effect demands.before.demands demands.after.demands) :
    ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget :=
  ResourceCertificationPipeline.mkFromParts demands.before demands.after effect hNI

end Cpp4
