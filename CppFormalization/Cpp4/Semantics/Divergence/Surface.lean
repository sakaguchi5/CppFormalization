import CppFormalization.Cpp4.Semantics.Divergence.Function

/-!
# CppFormalization.Cpp4.Semantics.Divergence.Surface

Surface divergence via expansion to ControlPlan.
-/

namespace Cpp4

namespace SurfaceDivergence

/-- A surface statement diverges when its expanded ControlPlan diverges. -/
def DivergesStmt (χ : KernelContext) (σ : State) (s : CppStmt) : Prop :=
  DivergesPlan χ σ (expandStmt s)

/-- A surface block diverges when its expanded PlanBlock diverges. -/
def DivergesBlock (χ : KernelContext) (σ : State) (b : StmtBlock) : Prop :=
  Cpp4.DivergesBlock χ σ (expandBlock b)

end SurfaceDivergence

end Cpp4
