import CppFormalization.Cpp4.Resource.Noninterference

/-!
# CppFormalization.Cpp4.Resource.Transport

The heart of Cpp4's lower design: execution effects transport future demands.
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

/-- Statement-boundary transport surface.  Boundary itself will be defined above
Resource as demand satisfaction for statement syntax. -/
structure StmtTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : StmtDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Block-boundary transport surface. -/
structure BlockTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : BlockDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

/-- Call-continuation transport surface. -/
structure CallTransport
    (χ χ' : DemandContext) (σ σ' : State)
    (eff : ResourceEffect) (before after : CallDemand) : Type where
  preserves : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands

end Cpp4
