import CppFormalization.Cpp4.Resource.Noninterference.All

/-!
# CppFormalization.Cpp4.Resource.Transport.Core

Demand transport across resource effects.
-/

namespace Cpp4

/-- Core demand transport theorem.

C++ reading: if the future demand `D` holds before an execution step and the
step's resource effect preserves that future demand as `D'`, then the future
demand holds after the step. -/
theorem demand_transport
    {χ χ' : DemandContext} {σ σ' : State}
    {eff : ResourceEffect} {D D' : DemandSet}
    (hD : DemandSetSatisfied χ σ D)
    (hPres : EffectPreservesDemand χ χ' σ σ' eff D D') :
    DemandSetSatisfied χ' σ' D' :=
  hPres.preserved hD

/-- Identity transport for unchanged states and demand contexts. -/
def demand_transport_refl
    {χ : DemandContext} {σ : State} {D : DemandSet} :
    EffectPreservesDemand χ χ σ σ [] D D := by
  constructor
  intro hD
  exact hD

end Cpp4
