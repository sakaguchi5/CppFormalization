import CppFormalization.Cpp4.Resource.Certification.Transport
import CppFormalization.Cpp4.Boundary.Transport.All

/-!
# CppFormalization.Cpp4.Resource.Certification.Boundary

Boundary-provider generation from the resource-certification pipeline.

This file keeps `Contracts` out of the current pass.  It only provides the
machine bridge:

`GeneratedDemand + GeneratedEffect + NoninterferenceCertificate`
  -> `EffectPreservesDemand`
  -> existing boundary transports.
-/

namespace Cpp4

/-- Generate the generic boundary transport from noninterference. -/
def boundaryTransport_of_noninterference
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {before after : DemandSet}
    (h : NoninterferenceCertificate χ χ' σ σ' eff before after) :
    BoundaryTransport χ χ' σ σ' eff before after where
  preserves := h.toEffectPreservesDemand

/-- Generate a typed expression-boundary transport from noninterference. -/
def exprBoundaryTransport_of_noninterference
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {e e' : ValExpr}
    {before : ExprTyping Γ e} {after : ExprTyping Γ' e'}
    (h : NoninterferenceCertificate χ χ' σ σ' eff
      before.demand.demands after.demand.demands) :
    ExprBoundaryTransport χ χ' σ σ' eff before after :=
  ExprBoundaryTransport.ofPreserves h.toEffectPreservesDemand

/-- Generate a typed condition-boundary transport from noninterference. -/
def condBoundaryTransport_of_noninterference
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {c c' : CppCond}
    {before : CondTyping Γ c} {after : CondTyping Γ' c'}
    (h : NoninterferenceCertificate χ χ' σ σ' eff
      before.demand.demands after.demand.demands) :
    CondBoundaryTransport χ χ' σ σ' eff before after where
  preserves := h.toEffectPreservesDemand

/-- Generate a typed ControlPlan-boundary transport from noninterference. -/
def planBoundaryTransport_of_noninterference
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {p p' : ControlPlan}
    {before : PlanTyping Γ κ p} {after : PlanTyping Γ' κ' p'}
    (h : NoninterferenceCertificate χ χ' σ σ' eff
      before.demand.demands after.demand.demands) :
    PlanBoundaryTransport χ χ' σ σ' eff before after :=
  PlanBoundaryTransport.ofPreserves h.toEffectPreservesDemand

/-- Generate a typed plan-block-boundary transport from noninterference. -/
def planBlockBoundaryTransport_of_noninterference
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {b b' : PlanBlock}
    {before : PlanBlockTyping Γ κ b} {after : PlanBlockTyping Γ' κ' b'}
    (h : NoninterferenceCertificate χ χ' σ σ' eff
      before.demand.demands after.demand.demands) :
    PlanBlockBoundaryTransport χ χ' σ σ' eff before after :=
  PlanBlockBoundaryTransport.ofPreserves h.toEffectPreservesDemand

end Cpp4
