import CppFormalization.Cpp4.Resource.Certification.Provider
import CppFormalization.Cpp4.Boundary.Transport.Block

/-!
# CppFormalization.Cpp4.Boundary.Transport.FromCertification

C2 entry points from the A/B/C1 certification pipeline to Boundary.Transport.

This file does not prove full C2.  It fixes the shape C2 should use: do not ask
for raw providers directly; ask for a `ResourceCertificationPipeline` whose pieces
come from A, B, and C1.
-/

namespace Cpp4

universe u v

namespace ResourceCertificationPipeline

/-- Generic boundary transport generated from a complete certification pipeline. -/
def toBoundaryTransport
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State}
    {beforeTarget : α} {afterTarget : β}
    (p : ResourceCertificationPipeline χ χ' σ σ' beforeTarget afterTarget) :
    BoundaryTransport χ χ' σ σ'
      p.generatedEffect.effect p.beforeDemand.demands p.afterDemand.demands where
  preserves := p.toEffectPreservesDemand

/-- Typed ControlPlan boundary transport generated from a pipeline whose demand
footprints are definitionally aligned with the two typing judgments. -/
def toPlanBoundaryTransport
    {χ χ' : DemandContext} {σ σ' : State}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {p p' : ControlPlan}
    {before : PlanTyping Γ κ p} {after : PlanTyping Γ' κ' p'}
    (cert : ResourceCertificationPipeline χ χ' σ σ' before after)
    (hBefore : cert.beforeDemand.demands = before.demand.demands)
    (hAfter : cert.afterDemand.demands = after.demand.demands) :
    PlanBoundaryTransport χ χ' σ σ' cert.generatedEffect.effect before after := by
  refine PlanBoundaryTransport.ofPreserves ?_
  rw [← hBefore, ← hAfter]
  exact cert.toEffectPreservesDemand

/-- Typed plan-block boundary transport generated from a pipeline whose demand
footprints are definitionally aligned with the two block typing judgments. -/
def toPlanBlockBoundaryTransport
    {χ χ' : DemandContext} {σ σ' : State}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {b b' : PlanBlock}
    {before : PlanBlockTyping Γ κ b} {after : PlanBlockTyping Γ' κ' b'}
    (cert : ResourceCertificationPipeline χ χ' σ σ' before after)
    (hBefore : cert.beforeDemand.demands = before.demand.demands)
    (hAfter : cert.afterDemand.demands = after.demand.demands) :
    PlanBlockBoundaryTransport χ χ' σ σ' cert.generatedEffect.effect before after := by
  refine PlanBlockBoundaryTransport.ofPreserves ?_
  rw [← hBefore, ← hAfter]
  exact cert.toEffectPreservesDemand

end ResourceCertificationPipeline

end Cpp4
