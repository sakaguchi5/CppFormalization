import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.While.Route.Condition

namespace Cpp
namespace CompoundContinuation
namespace While

/-!
# Body routes under a true condition
-/

structure BodyNormalRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (cond : ConditionTrueRoute entry)
    (σ1 : State) : Type where
  hbody : BigStepStmt σ body .normal σ1

structure BodyContinueRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (cond : ConditionTrueRoute entry)
    (σ1 : State) : Type where
  hbody : BigStepStmt σ body .continueResult σ1

structure BodyBreakRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (cond : ConditionTrueRoute entry)
    (σ1 : State) : Type where
  hbody : BigStepStmt σ body .breakResult σ1

structure BodyReturnRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (cond : ConditionTrueRoute entry)
    (rv : Option Value) (σ1 : State) : Type where
  hbody : BigStepStmt σ body (.returnResult rv) σ1

structure BodyDivergesRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (cond : ConditionTrueRoute entry) : Type where
  hbodyDiv : BigStepStmtDiv σ body

end While
end CompoundContinuation
end Cpp
