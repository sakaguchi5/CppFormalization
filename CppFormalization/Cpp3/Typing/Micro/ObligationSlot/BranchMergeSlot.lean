import CppFormalization.Cpp3.Typing.Micro.Composition.BranchMergeStatic
import CppFormalization.Cpp3.Contracts.Core.Policy

namespace Cpp3
namespace Typing
namespace Micro
namespace ObligationSlot

/-!
# CppFormalization.Cpp3.Typing.Micro.ObligationSlot.BranchMergeSlot

Obligation slot for runtime branch selection.

The static branch merge checks both branches.  A runtime proof later needs an
explicit place to state the C++ fact that evaluating the boolean condition
selects exactly one branch and that the selected branch boundary is the one that
continues.  This file names that place without supplying a global axiom.
-/

/-- A slot for the contract needed to continue from an `if` condition to the
selected branch in runtime state `σ`.

The concrete obligation is intentionally abstract here.  Later layers may
instantiate it with a selected-branch boundary, replay certificate, or adequacy
payload. -/
structure BranchSelectionSlot
    (Γ : TypeEnv) (σ : State) (c : ValExpr)
    (thenBranch elseBranch : CppStmt) : Type where
  kind : Contracts.ContractKind :=
    .obligation .branchMergeContinuation
  obligation : Prop
  evidence : Contracts.Requires obligation

namespace BranchSelectionSlot

/-- Extract the supplied program-facing branch-selection obligation evidence. -/
def get
    {Γ : TypeEnv} {σ : State} {c : ValExpr}
    {thenBranch elseBranch : CppStmt}
    (s : BranchSelectionSlot Γ σ c thenBranch elseBranch) : s.obligation :=
  s.evidence

end BranchSelectionSlot

end ObligationSlot
end Micro
end Typing
end Cpp3
