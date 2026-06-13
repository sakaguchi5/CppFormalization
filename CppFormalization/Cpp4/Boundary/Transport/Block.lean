import CppFormalization.Cpp4.Boundary.Transport.Plan
import CppFormalization.Cpp4.Boundary.Block
import CppFormalization.Cpp4.Resource.Transport.Plan

/-!
# CppFormalization.Cpp4.Boundary.Transport.Block

Transport for runtime boundaries of typed plan blocks.
-/

namespace Cpp4

/-- Transport from one typed plan-block boundary to another. -/
structure PlanBlockBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {b b' : PlanBlock}
    (before : PlanBlockTyping Γ κ b) (after : PlanBlockTyping Γ' κ' b') : Type where
  transport : PlanBlockTransport χ χ' σ σ' eff before.demand after.demand

namespace PlanBlockBoundaryTransport

/-- Apply plan-block-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {b b' : PlanBlock}
    {before : PlanBlockTyping Γ κ b} {after : PlanBlockTyping Γ' κ' b'}
    (bd : PlanBlockBoundary χ σ before)
    (t : PlanBlockBoundaryTransport χ χ' σ σ' eff before after) :
    PlanBlockBoundary χ' σ' after where
  demandsSatisfied := plan_block_transport bd.demandsSatisfied t.transport

/-- Build plan-block-boundary transport from a raw preservation certificate. -/
def ofPreserves
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {b b' : PlanBlock}
    {before : PlanBlockTyping Γ κ b} {after : PlanBlockTyping Γ' κ' b'}
    (h : EffectPreservesDemand χ χ' σ σ' eff before.demand.demands after.demand.demands) :
    PlanBlockBoundaryTransport χ χ' σ σ' eff before after where
  transport := { preserves := h }

end PlanBlockBoundaryTransport

end Cpp4
