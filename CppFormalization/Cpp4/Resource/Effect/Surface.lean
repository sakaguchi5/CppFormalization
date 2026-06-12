import CppFormalization.Cpp4.Core.Expand
import CppFormalization.Cpp4.Resource.Effect.Plan

/-!
# CppFormalization.Cpp4.Resource.Effect.Surface

Surface C++ effects as effects of expanded `ControlPlan`s.
-/

namespace Cpp4

/-- Resource effect surface for a C++ statement. -/
structure SurfaceStmtEffect where
  effect : ResourceEffect

/-- Resource effect surface for a C++ block. -/
structure SurfaceBlockEffect where
  effect : ResourceEffect

namespace SurfaceStmtEffect

/-- Surface effect from an already-computed plan effect. -/
def ofPlanEffect (e : PlanEffect) : SurfaceStmtEffect where
  effect := e.effect

/-- Structural surface effect via `expandStmt`. -/
def structural (s : CppStmt) : SurfaceStmtEffect :=
  ofPlanEffect (PlanEffect.structural (expandStmt s))

end SurfaceStmtEffect

namespace SurfaceBlockEffect

/-- Surface block effect from an already-computed plan-block effect. -/
def ofPlanBlockEffect (e : PlanBlockEffect) : SurfaceBlockEffect where
  effect := e.effect

/-- Structural surface block effect via `expandBlock`. -/
def structural (b : StmtBlock) : SurfaceBlockEffect :=
  ofPlanBlockEffect (PlanBlockEffect.structural (expandBlock b))

end SurfaceBlockEffect

end Cpp4
