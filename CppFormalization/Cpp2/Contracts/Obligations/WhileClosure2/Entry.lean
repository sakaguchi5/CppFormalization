import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.ReplayCore

namespace Cpp
namespace WhileClosure2

/-!
# While entry surface

The entry package says that the current state can start evaluating the while
statement.  It is intentionally local: it does not say anything about what
happens after the body runs.
-/

structure WhileEntry2
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  postState : PostStateAt Γ σ
  condReplay : ValueReplayAt Γ σ c (.base .bool)
  bodyReplay : StmtReplayAt Γ σ body

namespace WhileEntry2

def conditionReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntry2 Γ σ c body) :
    ExprReadyConcrete Γ σ c (.base .bool) :=
  h.condReplay.ready

def bodyReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntry2 Γ σ c body) :
    StmtReadyConcrete Γ σ body :=
  h.bodyReplay.ready

def whileReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntry2 Γ σ c body) :
    StmtReadyConcrete Γ σ (.whileStmt c body) :=
  StmtReadyConcrete.whileStmt
    h.condReplay.hasValueType
    h.condReplay.ready
    h.bodyReplay.ready

def toDynamicBoundary
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (h : WhileEntry2 Γ σ c body) :
    StmtContinuationDynamicBoundary Γ σ (.whileStmt c body) :=
  { state := h.postState.state
    safe := h.whileReady }

end WhileEntry2

end WhileClosure2
end Cpp
