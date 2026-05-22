import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.BodyRoute

namespace Cpp
namespace WhileClosure2

/-!
# Backedge replay

This is the genuinely C++-dependent while invariant layer.

After the body exits by `normal` or `continue`, the next iteration can only start
if the condition and body can be replayed in the post-state.
-/

structure NormalBackedgeReplay2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  postState : PostStateAt Γ σ'
  condReplay : ValueReplayAt Γ σ' c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ' body

structure ContinueBackedgeReplay2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  postState : PostStateAt Γ σ'
  condReplay : ValueReplayAt Γ σ' c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ' body

namespace NormalBackedgeReplay2

def whileReady
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalBackedgeReplay2 route) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

end NormalBackedgeReplay2

namespace ContinueBackedgeReplay2

def whileReady
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueBackedgeReplay2 route) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

end ContinueBackedgeReplay2

end WhileClosure2
end Cpp
