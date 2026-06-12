import CppFormalization.Cpp4.Core.Expand
import CppFormalization.Cpp4.Resource.Demand.Plan

/-!
# CppFormalization.Cpp4.Resource.Demand.Surface

Surface C++ demand as demand of its expanded `ControlPlan`.
-/

namespace Cpp4

/-- Resource demand required to enter a surface statement. -/
structure SurfaceStmtDemand where
  demands : DemandSet

/-- Resource demand required to enter a surface statement block. -/
structure SurfaceBlockDemand where
  demands : DemandSet

namespace SurfaceStmtDemand

/-- Surface demand from an already-computed plan demand. -/
def ofPlanDemand (d : PlanDemand) : SurfaceStmtDemand where
  demands := d.demands

/-- Structural surface demand via `expandStmt`. -/
def structural (s : CppStmt) : SurfaceStmtDemand :=
  ofPlanDemand (PlanDemand.structural (expandStmt s))

end SurfaceStmtDemand

namespace SurfaceBlockDemand

/-- Surface block demand from an already-computed plan-block demand. -/
def ofPlanBlockDemand (d : PlanBlockDemand) : SurfaceBlockDemand where
  demands := d.demands

/-- Structural surface block demand via `expandBlock`. -/
def structural (b : StmtBlock) : SurfaceBlockDemand :=
  ofPlanBlockDemand (PlanBlockDemand.structural (expandBlock b))

end SurfaceBlockDemand

end Cpp4
