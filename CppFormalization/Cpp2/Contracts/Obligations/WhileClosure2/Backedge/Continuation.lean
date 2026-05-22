import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Backedge.ReplayInvariant

namespace Cpp
namespace WhileClosure2

/-!
# Backedge continuation

Continuation is derived from post-state preservation plus replay invariants.
It is not an independent program contract.
-/

structure NormalBackedgeContinuationInput2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Prop where
  postState : NormalBackedgePostState2 route
  replay : NormalBackedgeReplayInvariant2 route

structure ContinueBackedgeContinuationInput2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Prop where
  postState : ContinueBackedgePostState2 route
  replay : ContinueBackedgeReplayInvariant2 route

namespace NormalBackedgeContinuationInput2

def whileReady
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalBackedgeContinuationInput2 route) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  h.replay.whileReady

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalBackedgeContinuationInput2 route) :
    StmtContinuationDynamicBoundary Γ σ' (.whileStmt c body) :=
  { state := h.postState.postState.state
    safe := h.whileReady }

end NormalBackedgeContinuationInput2

namespace ContinueBackedgeContinuationInput2

def whileReady
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueBackedgeContinuationInput2 route) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  h.replay.whileReady

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueBackedgeContinuationInput2 route) :
    StmtContinuationDynamicBoundary Γ σ' (.whileStmt c body) :=
  { state := h.postState.postState.state
    safe := h.whileReady }

end ContinueBackedgeContinuationInput2

end WhileClosure2
end Cpp
