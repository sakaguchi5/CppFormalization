import CppFormalization.Cpp3.Continuation.Core

/-!
# CppFormalization.Cpp3.Continuation.Branch

Continuation surfaces for selected `if` branches.
-/

namespace Cpp3
namespace Continuation

/-- Continuation from a condition route to the selected branch boundary. -/
structure SelectedBranchContinuation
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) (side : Semantics.BranchSide) : Type where
  stability : Stability.SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side

namespace SelectedBranchContinuation

/-- The source boundary for the whole if statement. -/
def source
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchContinuation Γ Γc σ σc cond thenBranch elseBranch side) :
    Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) :=
  h.stability.source

/-- The selected branch boundary package. -/
def target
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchContinuation Γ Γc σ σc cond thenBranch elseBranch side) :
    Boundary.SelectedBranchBoundary Γ Γc σ σc cond thenBranch elseBranch side :=
  h.stability.target

end SelectedBranchContinuation

/-- Specialization for the then branch. -/
abbrev ThenBranchContinuation
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type :=
  SelectedBranchContinuation Γ Γc σ σc cond thenBranch elseBranch
    Semantics.BranchSide.thenBranch

/-- Specialization for the else branch. -/
abbrev ElseBranchContinuation
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type :=
  SelectedBranchContinuation Γ Γc σ σc cond thenBranch elseBranch
    Semantics.BranchSide.elseBranch

end Continuation
end Cpp3
