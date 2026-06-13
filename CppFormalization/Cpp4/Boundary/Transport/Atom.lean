import CppFormalization.Cpp4.Boundary.Transport.Call
import CppFormalization.Cpp4.Boundary.Atom

/-!
# CppFormalization.Cpp4.Boundary.Transport.Atom

Transport for runtime boundaries of typed ControlPlan atoms.
-/

namespace Cpp4

/-- Transport from one typed-atom boundary to another. -/
structure AtomBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {a a' : ControlAtom}
    (before : PlanAtomTyping Γ κ a) (after : PlanAtomTyping Γ' κ' a') : Type where
  preserves :
    EffectPreservesDemand χ χ' σ σ' eff before.demand.demands after.demand.demands

namespace AtomBoundaryTransport

/-- Apply atom-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {a a' : ControlAtom}
    {before : PlanAtomTyping Γ κ a} {after : PlanAtomTyping Γ' κ' a'}
    (b : AtomBoundary χ σ before)
    (t : AtomBoundaryTransport χ χ' σ σ' eff before after) :
    AtomBoundary χ' σ' after where
  demandsSatisfied := demand_transport b.demandsSatisfied t.preserves

/-- View atom-boundary transport as raw demand-boundary transport. -/
def toDemandTransport
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {a a' : ControlAtom}
    {before : PlanAtomTyping Γ κ a} {after : PlanAtomTyping Γ' κ' a'}
    (t : AtomBoundaryTransport χ χ' σ σ' eff before after) :
    BoundaryTransport χ χ' σ σ' eff before.demand.demands after.demand.demands where
  preserves := t.preserves

end AtomBoundaryTransport

end Cpp4
