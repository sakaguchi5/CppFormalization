import CppFormalization.Cpp4.Boundary.Transport.Atom
import CppFormalization.Cpp4.Boundary.Plan
import CppFormalization.Cpp4.Resource.Transport.Plan

/-!
# CppFormalization.Cpp4.Boundary.Transport.Plan

Transport for runtime boundaries of typed ControlPlan values.
-/

namespace Cpp4

/-- Transport from one typed ControlPlan boundary to another. -/
structure PlanBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {p p' : ControlPlan}
    (before : PlanTyping Γ κ p) (after : PlanTyping Γ' κ' p') : Type where
  transport : PlanTransport χ χ' σ σ' eff before.demand after.demand

namespace PlanBoundaryTransport

/-- Apply ControlPlan-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {p p' : ControlPlan}
    {before : PlanTyping Γ κ p} {after : PlanTyping Γ' κ' p'}
    (b : PlanBoundary χ σ before)
    (t : PlanBoundaryTransport χ χ' σ σ' eff before after) :
    PlanBoundary χ' σ' after where
  demandsSatisfied := plan_transport b.demandsSatisfied t.transport

/-- Build ControlPlan-boundary transport from a raw preservation certificate. -/
def ofPreserves
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {p p' : ControlPlan}
    {before : PlanTyping Γ κ p} {after : PlanTyping Γ' κ' p'}
    (h : EffectPreservesDemand χ χ' σ σ' eff before.demand.demands after.demand.demands) :
    PlanBoundaryTransport χ χ' σ σ' eff before after where
  transport := { preserves := h }

/-- View ControlPlan-boundary transport as raw demand-boundary transport. -/
def toDemandTransport
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {p p' : ControlPlan}
    {before : PlanTyping Γ κ p} {after : PlanTyping Γ' κ' p'}
    (t : PlanBoundaryTransport χ χ' σ σ' eff before after) :
    BoundaryTransport χ χ' σ σ' eff before.demand.demands after.demand.demands where
  preserves := t.transport.preserves

end PlanBoundaryTransport

end Cpp4
