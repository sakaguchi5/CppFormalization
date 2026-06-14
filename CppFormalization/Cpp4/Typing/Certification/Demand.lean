import CppFormalization.Cpp4.Resource.Certification.Abstract
import CppFormalization.Cpp4.Typing.Judgment.Plan.All

/-!
# CppFormalization.Cpp4.Typing.Certification.Demand

Typing-side demand-footprint extraction for A.

This file stays below `Boundary`: it only exposes the demand footprints already
stored in typing judgments.  Boundary adequacy is connected above, in the Boundary
layer, so the global DAG remains

`Core -> Resource -> Typing -> Semantics -> Static -> Boundary -> Boundary.Transport`.
-/

namespace Cpp4

namespace PlanTyping

/-- Demand footprint exposed by a typed ControlPlan. -/
def demandFootprint {Γ : TypeEnv} {κ : ControlContext} {p : ControlPlan}
    (h : PlanTyping Γ κ p) : DemandFootprint p :=
  GeneratedDemand.ofDemandSet p h.demand.demands

/-- The footprint is definitionally the demand carried by the typing judgment. -/
theorem demandFootprint_demands {Γ : TypeEnv} {κ : ControlContext} {p : ControlPlan}
    (h : PlanTyping Γ κ p) :
    h.demandFootprint.demands = h.demand.demands :=
  rfl

/-- Future demand for a continuation/tail target, exposed without changing the
underlying typing judgment. -/
def futureDemandFootprint {Γ : TypeEnv} {κ : ControlContext} {p : ControlPlan}
    (h : PlanTyping Γ κ p) : DemandFootprint p :=
  h.demandFootprint

end PlanTyping

namespace PlanBlockTyping

/-- Demand footprint exposed by a typed plan block. -/
def demandFootprint {Γ : TypeEnv} {κ : ControlContext} {b : PlanBlock}
    (h : PlanBlockTyping Γ κ b) : DemandFootprint b :=
  GeneratedDemand.ofDemandSet b h.demand.demands

/-- The footprint is definitionally the demand carried by the block typing judgment. -/
theorem demandFootprint_demands {Γ : TypeEnv} {κ : ControlContext} {b : PlanBlock}
    (h : PlanBlockTyping Γ κ b) :
    h.demandFootprint.demands = h.demand.demands :=
  rfl

/-- Future demand for a block continuation/tail target. -/
def futureDemandFootprint {Γ : TypeEnv} {κ : ControlContext} {b : PlanBlock}
    (h : PlanBlockTyping Γ κ b) : DemandFootprint b :=
  h.demandFootprint

end PlanBlockTyping

/-- Demand-footprint pair for a ControlPlan transport obligation. -/
def planDemandFootprintPair
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext} {p p' : ControlPlan}
    (before : PlanTyping Γ κ p) (after : PlanTyping Γ' κ' p') :
    DemandFootprintPair before after where
  before := GeneratedDemand.ofDemandSet before before.demand.demands
  after := GeneratedDemand.ofDemandSet after after.demand.demands

/-- Demand-footprint pair for a plan-block transport obligation. -/
def planBlockDemandFootprintPair
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext} {b b' : PlanBlock}
    (before : PlanBlockTyping Γ κ b) (after : PlanBlockTyping Γ' κ' b') :
    DemandFootprintPair before after where
  before := GeneratedDemand.ofDemandSet before before.demand.demands
  after := GeneratedDemand.ofDemandSet after after.demand.demands

end Cpp4
