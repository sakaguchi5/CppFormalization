import CppFormalization.Cpp3.Typing.Micro.Composition.BranchMergeStatic

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.WhileStatic

Static channel components for `while (c) body`.

This file records only the typing-level shape of a while loop: the condition is
boolean, the body has the channels needed for reentry and exit, and an optional
return channel can be exposed.  Runtime backedge safety and replay stability are
left as explicit obligation slots for later layers.
-/

/-- The condition of a `while` statement is statically a boolean value expression. -/
structure WhileConditionStatic
    (Γ : TypeEnv) (c : ValExpr) : Prop where
  conditionBool : HasValueType Γ c (.base .bool)

namespace WhileConditionStatic

/-- Project the certified boolean typing evidence for the loop condition. -/
def certifiedCondition
    {Γ : TypeEnv} {c : ValExpr}
    (h : WhileConditionStatic Γ c) :
    Contracts.Certified (HasValueType Γ c (.base .bool)) :=
  h.conditionBool

/-- Use the generic branch-condition component when a later layer wants the
shared condition shape. -/
def toConditionBoolStatic
    {Γ : TypeEnv} {c : ValExpr}
    (h : WhileConditionStatic Γ c) :
    ConditionBoolStatic Γ c :=
  ⟨h.conditionBool⟩

end WhileConditionStatic

/-- Static body channels that can reenter or leave the loop normally.

The body is checked in the same type environment `Γ` for the normal, break, and
continue channels.  This is intentionally static only: it does not say that the
post-body runtime state can safely reenter the loop. -/
structure WhileReentryChannelsStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γ : TypeEnv) (body : CppStmt) : Prop where
  normalBody   : J .normalK Γ body Γ
  breakBody    : J .breakK Γ body Γ
  continueBody : J .continueK Γ body Γ

namespace WhileReentryChannelsStatic

/-- Project the certified normal-body channel. -/
def certifiedNormal
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ : TypeEnv} {body : CppStmt}
    (h : WhileReentryChannelsStatic J Γ body) :
    Contracts.Certified (J .normalK Γ body Γ) :=
  h.normalBody

/-- Project the certified break-body channel. -/
def certifiedBreak
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ : TypeEnv} {body : CppStmt}
    (h : WhileReentryChannelsStatic J Γ body) :
    Contracts.Certified (J .breakK Γ body Γ) :=
  h.breakBody

/-- Project the certified continue-body channel. -/
def certifiedContinue
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ : TypeEnv} {body : CppStmt}
    (h : WhileReentryChannelsStatic J Γ body) :
    Contracts.Certified (J .continueK Γ body Γ) :=
  h.continueBody

end WhileReentryChannelsStatic

/-- Optional static return channel exposed by the while body. -/
structure WhileReturnChannelStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γ Δ : TypeEnv) (body : CppStmt) : Prop where
  returnBody : J .returnK Γ body Δ

namespace WhileReturnChannelStatic

/-- Project the certified return-body channel. -/
def certifiedReturn
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Δ : TypeEnv} {body : CppStmt}
    (h : WhileReturnChannelStatic J Γ Δ body) :
    Contracts.Certified (J .returnK Γ body Δ) :=
  h.returnBody

end WhileReturnChannelStatic

/-- Complete static payload for the normal route of a `while` statement. -/
structure WhileNormalStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Prop where
  condition : WhileConditionStatic Γ c
  channels  : WhileReentryChannelsStatic J Γ body

namespace WhileNormalStatic

/-- Project the certified condition component. -/
def certifiedCondition
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalStatic J Γ c body) :
    Contracts.Certified (WhileConditionStatic Γ c) :=
  h.condition

/-- Project the certified reentry-channel component. -/
def certifiedChannels
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileNormalStatic J Γ c body) :
    Contracts.Certified (WhileReentryChannelsStatic J Γ body) :=
  h.channels

end WhileNormalStatic

/-- Complete static payload for the return route of a `while` statement. -/
structure WhileReturnStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γ Δ : TypeEnv) (c : ValExpr) (body : CppStmt) : Prop where
  normalPayload : WhileNormalStatic J Γ c body
  returnChannel : WhileReturnChannelStatic J Γ Δ body

namespace WhileReturnStatic

/-- Project the certified normal-route payload. -/
def certifiedNormalPayload
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileReturnStatic J Γ Δ c body) :
    Contracts.Certified (WhileNormalStatic J Γ c body) :=
  h.normalPayload

/-- Project the certified return-channel payload. -/
def certifiedReturnChannel
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Δ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (h : WhileReturnStatic J Γ Δ c body) :
    Contracts.Certified (WhileReturnChannelStatic J Γ Δ body) :=
  h.returnChannel

end WhileReturnStatic

end Composition
end Micro
end Typing
end Cpp3
