import CppFormalization.Cpp4.Typing.Certification.Demand
import CppFormalization.Cpp4.Boundary.Block

/-!
# CppFormalization.Cpp4.Boundary.Certification.Demand

Boundary-side adequacy bridge for A.

Typing extracts demand footprints below Boundary.  This file connects those
footprints to the current Boundary definitions, which are already demand-based.
-/

namespace Cpp4

namespace PlanTyping

/-- A satisfied typed-plan demand footprint is exactly a plan boundary. -/
def boundaryOfDemandFootprintSatisfied
    {χ : DemandContext} {σ : State}
    {Γ : TypeEnv} {κ : ControlContext} {p : ControlPlan}
    (h : PlanTyping Γ κ p)
    (hSat : GeneratedDemandSatisfied χ σ h.demandFootprint) :
    PlanBoundary χ σ h where
  demandsSatisfied := hSat.satisfied

end PlanTyping

namespace PlanBlockTyping

/-- A satisfied typed-block demand footprint is exactly a plan-block boundary. -/
def boundaryOfDemandFootprintSatisfied
    {χ : DemandContext} {σ : State}
    {Γ : TypeEnv} {κ : ControlContext} {b : PlanBlock}
    (h : PlanBlockTyping Γ κ b)
    (hSat : GeneratedDemandSatisfied χ σ h.demandFootprint) :
    PlanBlockBoundary χ σ h where
  demandsSatisfied := hSat.satisfied

end PlanBlockTyping

end Cpp4
