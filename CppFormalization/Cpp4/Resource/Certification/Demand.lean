import CppFormalization.Cpp4.Resource.Transport.Core
import CppFormalization.Cpp4.Resource.Demand.All

/-!
# CppFormalization.Cpp4.Resource.Certification.Demand

Demand-generation certificates for the resource-certification pipeline.

This layer deliberately does not introduce user-facing contracts.  It records the
machine-facing output of an analysis pass: the future demand set that a target
requires.  Later syntax/typing-specific analyzers can instantiate the polymorphic
`target` parameter with `ControlPlan`, `PlanBlock`, surface statements, functions,
or any smaller internal node.
-/

namespace Cpp4

universe u v

/-- A machine-generated future-demand set for a target object.

C++ reading: this is the resource footprint that must remain valid before the
corresponding target is entered or re-entered. -/
structure GeneratedDemand {α : Type u} (target : α) : Type u where
  demands : DemandSet

namespace GeneratedDemand

/-- Build a generated-demand certificate from an already computed demand set. -/
def ofDemandSet {α : Type u} (target : α) (D : DemandSet) : GeneratedDemand target where
  demands := D

/-- The empty generated demand. -/
def empty {α : Type u} (target : α) : GeneratedDemand target where
  demands := []

/-- View a generated demand as a statement demand. -/
def toStmtDemand {α : Type u} {target : α} (h : GeneratedDemand target) : StmtDemand where
  demands := h.demands

/-- View a generated demand as a block demand. -/
def toBlockDemand {α : Type u} {target : α} (h : GeneratedDemand target) : BlockDemand where
  demands := h.demands

/-- View a generated demand as an expression demand. -/
def toExprDemand {α : Type u} {target : α} (h : GeneratedDemand target) : ExprDemand where
  demands := h.demands

/-- View a generated demand as a call-continuation demand. -/
def toCallDemand {α : Type u} {target : α} (h : GeneratedDemand target) : CallDemand where
  demands := h.demands

end GeneratedDemand

/-- A pair of generated demands used by transport: the demand before an effect and
its demand after that effect. -/
structure GeneratedDemandTransition
    {α : Type u} {β : Type v} (beforeTarget : α) (afterTarget : β) : Type (max u v) where
  before : GeneratedDemand beforeTarget
  after : GeneratedDemand afterTarget

namespace GeneratedDemandTransition

/-- The before demand set of a generated transition. -/
def beforeDemands
    {α : Type u} {β : Type v} {beforeTarget : α} {afterTarget : β}
    (h : GeneratedDemandTransition beforeTarget afterTarget) : DemandSet :=
  h.before.demands

/-- The after demand set of a generated transition. -/
def afterDemands
    {α : Type u} {β : Type v} {beforeTarget : α} {afterTarget : β}
    (h : GeneratedDemandTransition beforeTarget afterTarget) : DemandSet :=
  h.after.demands

end GeneratedDemandTransition

/-- Runtime satisfaction of a generated demand.

This is intentionally separate from generation.  Generation says what is needed;
satisfaction says that the current state actually has it. -/
structure GeneratedDemandSatisfied
    {α : Type u} (χ : DemandContext) (σ : State) {target : α}
    (h : GeneratedDemand target) : Type u where
  satisfied : DemandSetSatisfied χ σ h.demands

namespace GeneratedDemandSatisfied

/-- Transport a satisfied generated demand along an already-proved raw demand
preservation certificate. -/
def transport
    {α : Type u} {β : Type v}
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {beforeTarget : α} {afterTarget : β}
    {before : GeneratedDemand beforeTarget} {after : GeneratedDemand afterTarget}
    (hSat : GeneratedDemandSatisfied χ σ before)
    (hPres : EffectPreservesDemand χ χ' σ σ' eff before.demands after.demands) :
    GeneratedDemandSatisfied χ' σ' after where
  satisfied := demand_transport hSat.satisfied hPres

end GeneratedDemandSatisfied

end Cpp4
