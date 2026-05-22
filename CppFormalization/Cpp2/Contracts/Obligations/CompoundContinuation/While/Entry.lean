import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.ReplayCore

namespace Cpp
namespace CompoundContinuation
namespace While

/-!
# While entry surface

Entry is local: it says the current state can start evaluating the while.
It does not say anything about what happens after the body runs.
-/

structure Entry
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  postState : PostStateAt Γ σ
  condReplay : ValueReplayAt Γ σ c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ body

namespace Entry

def conditionReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : Entry Γ σ c body) :
    ExprReadyConcrete Γ σ c (.base .bool) :=
  h.condReplay.ready

def bodyReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : Entry Γ σ c body) :
    StmtReadyConcrete Γ σ body :=
  h.bodyReplay.ready

def whileReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : Entry Γ σ c body) :
    StmtReadyConcrete Γ σ (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

def toDynamicBoundary
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : Entry Γ σ c body) :
    StmtContinuationDynamicBoundary Γ σ (.whileStmt c body) :=
  { state := h.postState.state
    safe := h.whileReady }

end Entry

end While
end CompoundContinuation
end Cpp
