import CppFormalization.Cpp4.Resource.Certification.Demand
import CppFormalization.Cpp4.Resource.Certification.Effect
import CppFormalization.Cpp4.Resource.Noninterference.DemandSet

/-!
# CppFormalization.Cpp4.Resource.Certification.Noninterference

The noninterference certificate used between demand/effect generation and raw
provider generation.

This is the middle layer that prevents `EffectPreservesDemand` from being handed
to soundness as an opaque assumption.  The certificate is still abstract enough to
be built from write/lifetime/scope/binding/call-specific facts, but it has a
single theorem-shaped output: demand-set preservation.
-/

namespace Cpp4

/-- A machine-facing noninterference certificate for a generated effect and a pair
of future-demand sets. -/
structure NoninterferenceCertificate
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (D D' : DemandSet) : Type where
  preserves : PreservesDemandSet χ χ' σ σ' eff D D'

namespace NoninterferenceCertificate

/-- Convert the machine-facing noninterference certificate into the raw provider
used by `Resource.Transport` and `Boundary.Transport`. -/
def toEffectPreservesDemand
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {D D' : DemandSet}
    (h : NoninterferenceCertificate χ χ' σ σ' eff D D') :
    EffectPreservesDemand χ χ' σ σ' eff D D' :=
  effectPreservesDemand_of_preservesDemandSet h.preserves

/-- Repackage a list-level preservation proof as a noninterference certificate. -/
def ofPreservesDemandSet
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {D D' : DemandSet}
    (h : PreservesDemandSet χ χ' σ σ' eff D D') :
    NoninterferenceCertificate χ χ' σ σ' eff D D' where
  preserves := h

/-- Empty demand-set noninterference. -/
def nil
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect} :
    NoninterferenceCertificate χ χ' σ σ' eff [] [] where
  preserves := PreservesDemandSet.nil

/-- Cons noninterference: one primitive demand plus the preserved tail. -/
def cons
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {d d' : ResourceDemand} {D D' : DemandSet}
    (hd : PreservesPrimitiveDemand χ χ' σ σ' eff d d')
    (hD : NoninterferenceCertificate χ χ' σ σ' eff D D') :
    NoninterferenceCertificate χ χ' σ σ' eff (d :: D) (d' :: D') where
  preserves := PreservesDemandSet.cons hd hD.preserves

/-- Append noninterference for two independently preserved demand fragments. -/
def append
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {D₁ D₂ D₁' D₂' : DemandSet}
    (h₁ : NoninterferenceCertificate χ χ' σ σ' eff D₁ D₁')
    (h₂ : NoninterferenceCertificate χ χ' σ σ' eff D₂ D₂') :
    NoninterferenceCertificate χ χ' σ σ' eff (D₁ ++ D₂) (D₁' ++ D₂') where
  preserves := PreservesDemandSet.append h₁.preserves h₂.preserves

/-- Same-demand noninterference when every primitive demand is preserved to itself. -/
def sameDemandsIfEach
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    (D : DemandSet)
    (h : ∀ d, d ∈ D → PreservesPrimitiveDemand χ χ' σ σ' eff d d) :
    NoninterferenceCertificate χ χ' σ σ' eff D D where
  preserves := PreservesDemandSet.sameDemandsIfEach D h

end NoninterferenceCertificate

end Cpp4
