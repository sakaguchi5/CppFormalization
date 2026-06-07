import CppFormalization.Cpp3.Typing.Micro.Composition.BranchMergeStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.BranchMergeSlot

Obligation slot for selected-branch boundary after condition evaluation.

The static branch merge checks both branches from the post-condition type
environment.  Runtime layers additionally need evidence that, after evaluating
the condition, the selected branch can actually be entered in the resulting
runtime state.

This is not the C++ branch-selection rule itself.  The semantic rule

  condition true  → execute then branch
  condition false → execute else branch

belongs to Semantics.  This slot only names the practical C++ obligation that the
condition evaluation did not destroy the boundary needed by the selected branch.

For example, a future side-effecting condition can make the selected branch
unsafe unless a stability proof explains why the branch boundary still holds.
-/

/-- A slot for the contract needed to continue from an `if` condition to the
selected branch in runtime state `σ`.

The concrete obligation is intentionally abstract here.  Later layers may
instantiate it with a condition-step certificate plus a selected-branch boundary
in the post-condition state.
-/
structure SelectedBranchBoundarySlot
    (Γ : TypeEnv) (σ : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type where
  kind : Contracts.ContractKind :=
    .obligation .branchBoundaryAfterCondition
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace SelectedBranchBoundarySlot

/-- Extract the supplied program-facing selected-branch-boundary obligation evidence. -/
def get
    {Γ : TypeEnv} {σ : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (s : SelectedBranchBoundarySlot Γ σ cond thenBranch elseBranch) : s.obligation :=
  s.evidence

end SelectedBranchBoundarySlot

end ObligationSlot
end Micro
end Typing
end Cpp3
