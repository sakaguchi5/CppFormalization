import CppFormalization.Cpp3.Typing.Micro.Composition.BlockConsStatic

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.BranchMergeStatic

Static components for `if c then s else t`.

This file keeps the typing-level shape of a branch separate from any runtime
claim about which branch is selected.  Runtime branch selection, replay, and
post-state readiness belong to later boundary/continuation/stability layers.
-/

/-- The condition of a branch is statically a boolean value expression. -/
structure ConditionBoolStatic
    (Γ : TypeEnv) (c : ValExpr) : Prop where
  conditionBool : HasValueType Γ c (.base .bool)

namespace ConditionBoolStatic

/-- Project the certified boolean typing evidence for the condition. -/
def certifiedCondition
    {Γ : TypeEnv} {c : ValExpr}
    (h : ConditionBoolStatic Γ c) :
    Contracts.Certified (HasValueType Γ c (.base .bool)) :=
  h.conditionBool

end ConditionBoolStatic

/-- Static same-channel/same-exit merge data for an `if` statement.

`BranchMergeStatic J k Γ Δ s t` says that both branches expose the same static
control channel `k` and the same static exit environment `Δ` when checked from
`Γ`.  It does not assert that both branches execute. -/
structure BranchMergeStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (k : ControlKind) (Γ Δ : TypeEnv) (thenBranch elseBranch : CppStmt) : Prop where
  thenTyping : J k Γ thenBranch Δ
  elseTyping : J k Γ elseBranch Δ

namespace BranchMergeStatic

/-- Project the certified then-branch typing evidence. -/
def certifiedThen
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {thenBranch elseBranch : CppStmt}
    (h : BranchMergeStatic J k Γ Δ thenBranch elseBranch) :
    Contracts.Certified (J k Γ thenBranch Δ) :=
  h.thenTyping

/-- Project the certified else-branch typing evidence. -/
def certifiedElse
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {thenBranch elseBranch : CppStmt}
    (h : BranchMergeStatic J k Γ Δ thenBranch elseBranch) :
    Contracts.Certified (J k Γ elseBranch Δ) :=
  h.elseTyping

end BranchMergeStatic

/-- Complete static typing payload for `if c then s else t`.

This is the Micro-level object from which the public statement judgment can be
reconstructed.  It contains only the static branch shape: a boolean condition and
a same-channel/same-exit branch merge. -/
structure IteStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (k : ControlKind) (Γ Δ : TypeEnv)
    (c : ValExpr) (thenBranch elseBranch : CppStmt) : Prop where
  condition : ConditionBoolStatic Γ c
  branches  : BranchMergeStatic J k Γ Δ thenBranch elseBranch

namespace IteStatic

/-- Project the certified condition component. -/
def certifiedCondition
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr}
    {thenBranch elseBranch : CppStmt}
    (h : IteStatic J k Γ Δ c thenBranch elseBranch) :
    Contracts.Certified (ConditionBoolStatic Γ c) :=
  h.condition

/-- Project the certified branch-merge component. -/
def certifiedBranches
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {k : ControlKind} {Γ Δ : TypeEnv} {c : ValExpr}
    {thenBranch elseBranch : CppStmt}
    (h : IteStatic J k Γ Δ c thenBranch elseBranch) :
    Contracts.Certified (BranchMergeStatic J k Γ Δ thenBranch elseBranch) :=
  h.branches

end IteStatic

end Composition
end Micro
end Typing
end Cpp3
