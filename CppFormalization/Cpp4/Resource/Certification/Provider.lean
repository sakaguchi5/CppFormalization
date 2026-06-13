import CppFormalization.Cpp4.Resource.Certification.Noninterference

/-!
# CppFormalization.Cpp4.Resource.Certification.Provider

Provider generation for the resource-certification pipeline.

This file ties together the four machine stages:

1. generated future demands,
2. generated resource effect,
3. noninterference certificate,
4. generated raw provider `EffectPreservesDemand`.
-/

namespace Cpp4

universe u v

/-- The complete machine pipeline for one transport obligation.

`beforeTarget` and `afterTarget` are intentionally polymorphic.  They can be plan
nodes, surface nodes, loop re-entry points, switch suffixes, function bodies, or
later checker artifacts. -/
structure ResourceCertificationPipeline
    {α : Type u} {β : Type v}
    (χ χ' : DemandContext) (σ σ' : State)
    (beforeTarget : α) (afterTarget : β) : Type (max u v) where
  beforeDemand : GeneratedDemand beforeTarget
  afterDemand : GeneratedDemand afterTarget
  generatedEffect : GeneratedEffect σ σ'
  noninterference :
    NoninterferenceCertificate χ χ' σ σ'
      generatedEffect.effect beforeDemand.demands afterDemand.demands

namespace ResourceCertificationPipeline

/-- The generated before-demand set. -/
def beforeDemands
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (p : ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget) : DemandSet :=
  p.beforeDemand.demands

/-- The generated after-demand set. -/
def afterDemands
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (p : ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget) : DemandSet :=
  p.afterDemand.demands

/-- The generated resource-effect list. -/
def effect
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (p : ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget) : ResourceEffect :=
  p.generatedEffect.effect

/-- Stage 4: turn demand generation, effect generation, and noninterference into
the raw provider expected by transport layers. -/
def toEffectPreservesDemand
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (p : ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget) :
    EffectPreservesDemand χ χ' σ σ'
      p.generatedEffect.effect p.beforeDemand.demands p.afterDemand.demands :=
  p.noninterference.toEffectPreservesDemand

/-- Apply the generated provider to an already satisfied generated demand. -/
def transportSatisfied
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (p : ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget)
    (hSat : GeneratedDemandSatisfied χ σ p.beforeDemand) :
    GeneratedDemandSatisfied χ' σ' p.afterDemand :=
  hSat.transport p.toEffectPreservesDemand

/-- Build the pipeline from explicit pieces. -/
def mkFromParts
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (beforeDemand : GeneratedDemand beforeTarget)
    (afterDemand : GeneratedDemand afterTarget)
    (generatedEffect : GeneratedEffect σ σ')
    (hNI : NoninterferenceCertificate χ χ' σ σ'
      generatedEffect.effect beforeDemand.demands afterDemand.demands) :
    ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget where
  beforeDemand := beforeDemand
  afterDemand := afterDemand
  generatedEffect := generatedEffect
  noninterference := hNI

end ResourceCertificationPipeline

end Cpp4
