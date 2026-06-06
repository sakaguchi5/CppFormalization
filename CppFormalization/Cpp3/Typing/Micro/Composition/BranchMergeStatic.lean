import CppFormalization.Cpp3.Typing.Micro.Composition.BlockConsStatic

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.BranchMergeStatic

Static components for `if cond then s else t`.

The condition is a third syntax category (`CppCond`), not a raw `ValExpr`.  This
keeps the shared lifecycle of `if` and `while` conditions visible: static
condition typing, runtime condition evaluation, replay, and post-condition
boundary reconstruction.
-/

/-- Project the certified condition typing evidence. -/
def certifiedCondition
    {Γ Γc : TypeEnv} {cond : CppCond}
    (h : ConditionStatic Γ cond Γc) :
    Contracts.Certified (ConditionStatic Γ cond Γc) :=
  h

/-- Static same-channel/same-exit merge data for an `if` statement.

`BranchMergeStatic J k Γc Δ s t` says that both branches expose the same static
control channel `k` and the same static exit environment `Δ` when checked from
the post-condition type environment `Γc`.  It does not assert that both branches
execute. -/
structure BranchMergeStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (k : ControlKind) (Γc Δ : TypeEnv) (thenBranch elseBranch : CppStmt) : Prop where
  thenTyping : J k Γc thenBranch Δ
  elseTyping : J k Γc elseBranch Δ

namespace BranchMergeStatic

/-- Project the certified then-branch typing evidence. -/
def certifiedThen
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γc Δ : TypeEnv} {thenBranch elseBranch : CppStmt}
    (h : BranchMergeStatic J k Γc Δ thenBranch elseBranch) :
    Contracts.Certified (J k Γc thenBranch Δ) :=
  h.thenTyping

/-- Project the certified else-branch typing evidence. -/
def certifiedElse
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γc Δ : TypeEnv} {thenBranch elseBranch : CppStmt}
    (h : BranchMergeStatic J k Γc Δ thenBranch elseBranch) :
    Contracts.Certified (J k Γc elseBranch Δ) :=
  h.elseTyping

end BranchMergeStatic

/-- Complete static typing payload for `if cond then s else t`.

The condition is checked from `Γ` and exposes a post-condition environment `Γc`;
both branches are checked from `Γc`.  Runtime branch selection and selected
branch boundary validity belong to later semantics/boundary/stability layers. -/
structure IteStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (k : ControlKind) (Γ Γc Δ : TypeEnv)
    (cond : CppCond) (thenBranch elseBranch : CppStmt) : Prop where
  condition : ConditionStatic Γ cond Γc
  branches  : BranchMergeStatic J k Γc Δ thenBranch elseBranch

namespace IteStatic

/-- Project the certified condition component. -/
def certifiedCondition
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Γc Δ : TypeEnv} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (h : IteStatic J k Γ Γc Δ cond thenBranch elseBranch) :
    Contracts.Certified (ConditionStatic Γ cond Γc) :=
  h.condition

/-- Project the certified branch-merge component. -/
def certifiedBranches
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Γc Δ : TypeEnv} {cond : CppCond}
    {thenBranch elseBranch : CppStmt}
    (h : IteStatic J k Γ Γc Δ cond thenBranch elseBranch) :
    Contracts.Certified (BranchMergeStatic J k Γc Δ thenBranch elseBranch) :=
  h.branches

end IteStatic

end Composition
end Micro
end Typing
end Cpp3
