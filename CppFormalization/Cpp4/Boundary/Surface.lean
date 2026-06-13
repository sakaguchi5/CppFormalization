import CppFormalization.Cpp4.Boundary.Switch
import CppFormalization.Cpp4.Typing.Judgment.Surface.Switch
import CppFormalization.Cpp4.Typing.Judgment.Expand

/-!
# CppFormalization.Cpp4.Boundary.Surface

Runtime boundaries for typed surface statements and their expanded plans.
-/

namespace Cpp4

/-- A typed surface statement is enterable when its surface demand is satisfied. -/
structure SurfaceStmtBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {s : CppStmt} (h : SurfaceStmtTyping Γ κ s) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace SurfaceStmtBoundary

/-- Repackage a surface-statement boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {s : CppStmt} {h : SurfaceStmtTyping Γ κ s} (b : SurfaceStmtBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := b.demandsSatisfied

/-- Build a surface-statement boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {s : CppStmt} {h : SurfaceStmtTyping Γ κ s}
    (b : DemandBoundary χ σ h.demand.demands) : SurfaceStmtBoundary χ σ h where
  demandsSatisfied := b.satisfied

/-- Formation evidence stored by the surface-statement typing certificate. -/
def formationEvidence {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {s : CppStmt} {h : SurfaceStmtTyping Γ κ s} (_b : SurfaceStmtBoundary χ σ h) :
    h.formation :=
  h.evidence

end SurfaceStmtBoundary

/-- A typed surface block is enterable when its surface block demand is satisfied. -/
structure SurfaceBlockBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {b : StmtBlock} (h : SurfaceBlockTyping Γ κ b) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

namespace SurfaceBlockBoundary

/-- Repackage a surface-block boundary as a generic demand boundary. -/
def toDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {b : StmtBlock} {h : SurfaceBlockTyping Γ κ b} (bd : SurfaceBlockBoundary χ σ h) :
    DemandBoundary χ σ h.demand.demands where
  satisfied := bd.demandsSatisfied

/-- Build a surface-block boundary from a generic demand boundary. -/
def ofDemandBoundary {χ : DemandContext} {σ : State} {Γ : TypeEnv} {κ : ControlContext}
    {b : StmtBlock} {h : SurfaceBlockTyping Γ κ b}
    (bd : DemandBoundary χ σ h.demand.demands) : SurfaceBlockBoundary χ σ h where
  demandsSatisfied := bd.satisfied

end SurfaceBlockBoundary

/-- A typed surface loop is enterable when its loop demand is satisfied. -/
structure SurfaceLoopBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {l : CppLoop} (h : SurfaceLoopTyping Γ κ l) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

/-- A typed surface switch is enterable when its switch demand is satisfied. -/
structure SurfaceSwitchBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {cond : CppSwitchCond} {arms : SwitchArmList}
    (h : SurfaceSwitchTyping Γ κ cond arms) : Type where
  demandsSatisfied : DemandSetSatisfied χ σ h.demand.demands

/-- Bridge boundary: a surface statement together with an expanded plan typing and
its plan boundary.  This is the shape used when returning from Plan soundness to
surface C++ soundness. -/
structure ExpandedSurfaceStmtBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {s : CppStmt} (hSurface : SurfaceStmtTyping Γ κ s)
    (hPlan : PlanTyping Γ κ (expandStmt s)) : Type where
  surfaceBoundary : SurfaceStmtBoundary χ σ hSurface
  planBoundary : PlanBoundary χ σ hPlan

/-- Bridge boundary for a surface block and its expanded plan block. -/
structure ExpandedSurfaceBlockBoundary
    (χ : DemandContext) (σ : State) {Γ : TypeEnv} {κ : ControlContext}
    {b : StmtBlock} (hSurface : SurfaceBlockTyping Γ κ b)
    (hPlan : PlanBlockTyping Γ κ (expandBlock b)) : Type where
  surfaceBoundary : SurfaceBlockBoundary χ σ hSurface
  planBoundary : PlanBlockBoundary χ σ hPlan

end Cpp4
