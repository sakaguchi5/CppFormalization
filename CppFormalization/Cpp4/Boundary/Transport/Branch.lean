import CppFormalization.Cpp4.Boundary.Transport.Seq

/-!
# CppFormalization.Cpp4.Boundary.Transport.Branch

Selected-branch boundary transport.
-/

namespace Cpp4

/-- Transport certificate for the selected branch after a condition step. -/
structure BranchSelectedBoundaryTransport
    (χ χ' : DemandContext) (σ σ' : State) (eff : ResourceEffect)
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {branch branch' : ControlPlan}
    (beforeBranch : PlanTyping Γ κ branch) (afterBranch : PlanTyping Γ' κ' branch') : Type where
  branchTransport : PlanBoundaryTransport χ χ' σ σ' eff beforeBranch afterBranch

namespace BranchSelectedBoundaryTransport

/-- Apply selected-branch transport. -/
def apply
    {χ χ' : DemandContext} {σ σ' : State} {eff : ResourceEffect}
    {Γ Γ' : TypeEnv} {κ κ' : ControlContext}
    {branch branch' : ControlPlan}
    {beforeBranch : PlanTyping Γ κ branch} {afterBranch : PlanTyping Γ' κ' branch'}
    (bBranch : PlanBoundary χ σ beforeBranch)
    (t : BranchSelectedBoundaryTransport χ χ' σ σ' eff beforeBranch afterBranch) :
    PlanBoundary χ' σ' afterBranch :=
  PlanBoundaryTransport.apply bBranch t.branchTransport

end BranchSelectedBoundaryTransport

/-- True branch selected by the condition. -/
abbrev BranchThenBoundaryTransport := BranchSelectedBoundaryTransport

/-- False branch selected by the condition. -/
abbrev BranchElseBoundaryTransport := BranchSelectedBoundaryTransport

end Cpp4
