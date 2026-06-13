import CppFormalization.Cpp4.Boundary.Transport.Function
import CppFormalization.Cpp4.Boundary.Surface
import CppFormalization.Cpp4.Resource.Transport.Surface

/-!
# CppFormalization.Cpp4.Boundary.Transport.Surface

Boundary transport for surface statements and blocks.
-/

namespace Cpp4

/-- Transport from one typed surface-statement boundary to another. -/
structure SurfaceStmtBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {s s' : CppStmt}
    (before : SurfaceStmtTyping Γ κ s) (after : SurfaceStmtTyping Γ' κ' s') : Type where
  transport : SurfaceStmtTransport χ χ' σ σ' eff before.demand after.demand

namespace SurfaceStmtBoundaryTransport

/-- Apply surface-statement-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {s s' : CppStmt}
    {before : SurfaceStmtTyping Γ κ s} {after : SurfaceStmtTyping Γ' κ' s'}
    (b : SurfaceStmtBoundary χ σ before)
    (t : SurfaceStmtBoundaryTransport χ χ' σ σ' eff before after) :
    SurfaceStmtBoundary χ' σ' after where
  demandsSatisfied := surface_stmt_transport b.demandsSatisfied t.transport

/-- Build surface-statement boundary transport from expanded plan transport. -/
def ofPlanTransport
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {s s' : CppStmt}
    {before : SurfaceStmtTyping Γ κ s} {after : SurfaceStmtTyping Γ' κ' s'}
    {pBefore : PlanTyping Γ κ (expandStmt s)}
    {pAfter : PlanTyping Γ' κ' (expandStmt s')}
    (hPlan : PlanBoundaryTransport χ χ' σ σ' eff pBefore pAfter)
    (hBeforeDemand : before.demand.demands = pBefore.demand.demands)
    (hAfterDemand : after.demand.demands = pAfter.demand.demands) :
    SurfaceStmtBoundaryTransport χ χ' σ σ' eff before after where
  transport :=
    { preserves := by
        constructor
        intro hD
        rw [hBeforeDemand] at hD
        have hAfter : DemandSetSatisfied χ' σ' pAfter.demand.demands :=
          demand_transport hD hPlan.transport.preserves
        rw [hAfterDemand]
        exact hAfter }

end SurfaceStmtBoundaryTransport

/-- Transport from one typed surface-block boundary to another. -/
structure SurfaceBlockBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {b b' : StmtBlock}
    (before : SurfaceBlockTyping Γ κ b) (after : SurfaceBlockTyping Γ' κ' b') : Type where
  transport : SurfaceBlockTransport χ χ' σ σ' eff before.demand after.demand

namespace SurfaceBlockBoundaryTransport

/-- Apply surface-block-boundary transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {b b' : StmtBlock}
    {before : SurfaceBlockTyping Γ κ b} {after : SurfaceBlockTyping Γ' κ' b'}
    (bd : SurfaceBlockBoundary χ σ before)
    (t : SurfaceBlockBoundaryTransport χ χ' σ σ' eff before after) :
    SurfaceBlockBoundary χ' σ' after where
  demandsSatisfied := surface_block_transport bd.demandsSatisfied t.transport

end SurfaceBlockBoundaryTransport

/-- Transport for expanded surface statement boundaries. -/
structure ExpandedSurfaceStmtBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {s s' : CppStmt}
    {surfaceBefore : SurfaceStmtTyping Γ κ s}
    {surfaceAfter : SurfaceStmtTyping Γ' κ' s'}
    {planBefore : PlanTyping Γ κ (expandStmt s)}
    {planAfter : PlanTyping Γ' κ' (expandStmt s')}
    (before : ExpandedSurfaceStmtBoundary χ σ surfaceBefore planBefore)
    (afterSurface : SurfaceStmtTyping Γ' κ' s')
    (afterPlan : PlanTyping Γ' κ' (expandStmt s')) : Type where
  surfaceTransport : SurfaceStmtBoundaryTransport χ χ' σ σ' eff surfaceBefore afterSurface
  planTransport : PlanBoundaryTransport χ χ' σ σ' eff planBefore afterPlan

end Cpp4
