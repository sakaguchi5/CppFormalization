import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.ConditionRoute

namespace Cpp
namespace WhileClosure2

/-!
# Body routes under a true condition

These routes are only available after the condition has evaluated to true.
They separate the five meaningful body outcomes: normal, continue, break,
return, and divergence.
-/

structure BodyNormalRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (cond : ConditionTrueRoute2 entry)
    (σ' : State) : Type where
  hbody : BigStepStmt σ body .normal σ'

structure BodyContinueRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (cond : ConditionTrueRoute2 entry)
    (σ' : State) : Type where
  hbody : BigStepStmt σ body .continueResult σ'

structure BodyBreakRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (cond : ConditionTrueRoute2 entry)
    (σ' : State) : Type where
  hbody : BigStepStmt σ body .breakResult σ'

structure BodyReturnRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (cond : ConditionTrueRoute2 entry)
    (rv : Option Value) (σ' : State) : Type where
  hbody : BigStepStmt σ body (.returnResult rv) σ'

structure BodyDivergesRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (cond : ConditionTrueRoute2 entry) : Type where
  hbodyDiv : BigStepStmtDiv σ body

end WhileClosure2
end Cpp
