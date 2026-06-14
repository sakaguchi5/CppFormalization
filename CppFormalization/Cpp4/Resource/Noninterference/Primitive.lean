import CppFormalization.Cpp4.Resource.Noninterference.DemandSet

/-!
# CppFormalization.Cpp4.Resource.Noninterference.Primitive

Small C1 helpers for primitive-demand preservation.

These definitions deliberately stay below `Resource.Certification`: primitive
noninterference should be proved in Resource, and only later packaged as
certification-level providers.
-/

namespace Cpp4

namespace PreservesPrimitiveDemand

/-- Build primitive preservation from the underlying implication. -/
def ofPreserved
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {d d' : ResourceDemand}
    (h : DemandSatisfied χ σ d → DemandSatisfied χ' σ' d') :
    PreservesPrimitiveDemand χ χ' σ σ' eff d d' where
  preserved := h

/-- Lift primitive preservation to singleton demand-set preservation. -/
def toSingletonPreservesDemandSet
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {d d' : ResourceDemand}
    (h : PreservesPrimitiveDemand χ χ' σ σ' eff d d') :
    PreservesDemandSet χ χ' σ σ' eff [d] [d'] :=
  PreservesDemandSet.cons h PreservesDemandSet.nil

end PreservesPrimitiveDemand

/-- Named synonym for the common C1 shape: an effect preserves one demand to itself. -/
abbrev PreservesSamePrimitiveDemand
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (d : ResourceDemand) : Type :=
  PreservesPrimitiveDemand χ χ' σ σ' eff d d

end Cpp4
