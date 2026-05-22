import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Backedge.PostState

namespace Cpp
namespace WhileClosure2

/-!
# Backedge replay invariants

After the body exits by `normal` or `continue`, the next iteration can only
start if the condition and body can be replayed in the post-state.

This is the C++-dependent invariant layer.  It deliberately does not include
post-state preservation.
-/

structure NormalBackedgeReplayInvariant2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Prop where
  condReplay : ValueReplayAt Γ σ' c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ' body

structure ContinueBackedgeReplayInvariant2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Prop where
  condReplay : ValueReplayAt Γ σ' c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ' body

namespace NormalBackedgeReplayInvariant2

def whileReady
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalBackedgeReplayInvariant2 route) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

end NormalBackedgeReplayInvariant2

namespace ContinueBackedgeReplayInvariant2

def whileReady
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueBackedgeReplayInvariant2 route) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

end ContinueBackedgeReplayInvariant2

end WhileClosure2
end Cpp
