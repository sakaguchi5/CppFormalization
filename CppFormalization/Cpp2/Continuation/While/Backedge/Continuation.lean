import CppFormalization.Cpp2.Route.While.Body

namespace Cpp
namespace CompoundContinuation
namespace While
namespace Backedge

/-!
# While backedge continuation

Post-state preservation and replay invariants are separated.  The continuation
boundary is derived from those two ingredients.
-/

structure NormalPostState
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyNormalRoute cond σ1) : Prop where
  postState : PostStateAt Γ σ1

structure ContinuePostState
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyContinueRoute cond σ1) : Prop where
  postState : PostStateAt Γ σ1

structure NormalReplayInvariant
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyNormalRoute cond σ1) : Prop where
  condReplay : ValueReplayAt Γ σ1 c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ1 body

structure ContinueReplayInvariant
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyContinueRoute cond σ1) : Prop where
  condReplay : ValueReplayAt Γ σ1 c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ1 body

namespace NormalReplayInvariant

def whileReady
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (h : NormalReplayInvariant route) :
    StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

end NormalReplayInvariant

namespace ContinueReplayInvariant

def whileReady
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (h : ContinueReplayInvariant route) :
    StmtReadyConcrete Γ σ1 (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

end ContinueReplayInvariant

structure NormalContinuationInput
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyNormalRoute cond σ1) : Prop where
  postState : NormalPostState route
  replay : NormalReplayInvariant route

structure ContinueContinuationInput
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyContinueRoute cond σ1) : Prop where
  postState : ContinuePostState route
  replay : ContinueReplayInvariant route

namespace NormalContinuationInput

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (h : NormalContinuationInput route) :
    StmtContinuationDynamicBoundary Γ σ1 (.whileStmt c body) :=
  { state := h.postState.postState.state
    safe := h.replay.whileReady }

end NormalContinuationInput

namespace ContinueContinuationInput

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (h : ContinueContinuationInput route) :
    StmtContinuationDynamicBoundary Γ σ1 (.whileStmt c body) :=
  { state := h.postState.postState.state
    safe := h.replay.whileReady }

end ContinueContinuationInput

end Backedge
end While
end CompoundContinuation
end Cpp
