import CppFormalization.Cpp3.Typing.Micro.Composition.BranchMergeStatic

namespace Cpp3
namespace Typing
namespace Micro
namespace Composition

/-!
# CppFormalization.Cpp3.Typing.Micro.Composition.WhileStatic

Static channel components for `while (cond) body`.

The condition is a `CppCond`.  This file records only the typing-level shape of
a while loop: the condition exposes a post-condition environment, the body has
the channels needed for reentry and exit, and an optional return channel can be
exposed.  Runtime backedge safety and replay stability are left as explicit
demands for later layers.
-/

/-- Static body channels that can reenter or leave the loop normally.

The body is checked in the post-condition type environment `Γc`.  Normal, break,
and continue routes return to the outer loop environment `Γ`.  This is
intentionally static only: it does not say that the post-body runtime state can
safely reenter the loop condition. -/
structure WhileReentryChannelsStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γ Γc : TypeEnv) (body : CppStmt) : Prop where
  normalBody   : J .normalK Γc body Γ
  breakBody    : J .breakK Γc body Γ
  continueBody : J .continueK Γc body Γ

namespace WhileReentryChannelsStatic

/-- Project the certified normal-body channel. -/
def certifiedNormal
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Γc : TypeEnv} {body : CppStmt}
    (h : WhileReentryChannelsStatic J Γ Γc body) :
    Contracts.Certified (J .normalK Γc body Γ) :=
  h.normalBody

/-- Project the certified break-body channel. -/
def certifiedBreak
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Γc : TypeEnv} {body : CppStmt}
    (h : WhileReentryChannelsStatic J Γ Γc body) :
    Contracts.Certified (J .breakK Γc body Γ) :=
  h.breakBody

/-- Project the certified continue-body channel. -/
def certifiedContinue
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Γc : TypeEnv} {body : CppStmt}
    (h : WhileReentryChannelsStatic J Γ Γc body) :
    Contracts.Certified (J .continueK Γc body Γ) :=
  h.continueBody

end WhileReentryChannelsStatic

/-- Optional static return channel exposed by the while body. -/
structure WhileReturnChannelStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γc Δ : TypeEnv) (body : CppStmt) : Prop where
  returnBody : J .returnK Γc body Δ

namespace WhileReturnChannelStatic

/-- Project the certified return-body channel. -/
def certifiedReturn
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γc Δ : TypeEnv} {body : CppStmt}
    (h : WhileReturnChannelStatic J Γc Δ body) :
    Contracts.Certified (J .returnK Γc body Δ) :=
  h.returnBody

end WhileReturnChannelStatic

/-- Complete static payload for the normal route of a `while` statement. -/
structure WhileNormalStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Prop where
  condition : ConditionStatic Γ cond Γc
  channels  : WhileReentryChannelsStatic J Γ Γc body

namespace WhileNormalStatic

/-- Project the certified condition component. -/
def certifiedCondition
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileNormalStatic J Γ Γc cond body) :
    Contracts.Certified (ConditionStatic Γ cond Γc) :=
  h.condition

/-- Project the certified reentry-channel component. -/
def certifiedChannels
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Γc : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileNormalStatic J Γ Γc cond body) :
    Contracts.Certified (WhileReentryChannelsStatic J Γ Γc body) :=
  h.channels

end WhileNormalStatic

/-- Complete static payload for the return route of a `while` statement. -/
structure WhileReturnStatic
    (J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop)
    (Γ Γc Δ : TypeEnv) (cond : CppCond) (body : CppStmt) : Prop where
  normalPayload : WhileNormalStatic J Γ Γc cond body
  returnChannel : WhileReturnChannelStatic J Γc Δ body

namespace WhileReturnStatic

/-- Project the certified normal-route payload. -/
def certifiedNormalPayload
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Γc Δ : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileReturnStatic J Γ Γc Δ cond body) :
    Contracts.Certified (WhileNormalStatic J Γ Γc cond body) :=
  h.normalPayload

/-- Project the certified return-channel payload. -/
def certifiedReturnChannel
    {J : ControlKind → TypeEnv → CppStmt → TypeEnv → Prop}
    {Γ Γc Δ : TypeEnv} {cond : CppCond} {body : CppStmt}
    (h : WhileReturnStatic J Γ Γc Δ cond body) :
    Contracts.Certified (WhileReturnChannelStatic J Γc Δ body) :=
  h.returnChannel

end WhileReturnStatic

end Composition
end Micro
end Typing
end Cpp3
