import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.BackedgeReplay

namespace Cpp
namespace WhileClosure2

/-!
# Backedge continuation

This layer turns post-state replay into a dynamic continuation boundary for the
same while statement.
-/

namespace NormalBackedgeReplay2

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalBackedgeReplay2 route) :
    StmtContinuationDynamicBoundary Γ σ' (.whileStmt c body) :=
  { state := h.postState.state
    safe := h.whileReady }

end NormalBackedgeReplay2

namespace ContinueBackedgeReplay2

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueBackedgeReplay2 route) :
    StmtContinuationDynamicBoundary Γ σ' (.whileStmt c body) :=
  { state := h.postState.state
    safe := h.whileReady }

end ContinueBackedgeReplay2

end WhileClosure2
end Cpp
