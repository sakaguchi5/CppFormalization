import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Route.Body

namespace Cpp
namespace WhileClosure2

/-!
# Non-tail exit lifting

These are theorem-backed semantic liftings for the non-tail while exits.

The only exception is condition divergence: the current semantics has no
separate expression-divergence object, so `ConditionDivergesRoute2` already
stores the lifted while divergence fact.
-/

namespace ExitLifting2

theorem whileStepOfConditionFalse
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (route : ConditionFalseRoute2 entry) :
    BigStepStmt σ (.whileStmt c body) .normal σ := by
  exact BigStepStmt.whileFalse route.hcondFalse

theorem whileStepOfBodyBreak
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyBreakRoute2 cond σ') :
    BigStepStmt σ (.whileStmt c body) .normal σ' := by
  exact BigStepStmt.whileTrueBreak cond.hcondTrue route.hbody

theorem whileStepOfBodyReturn
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {rv : Option Value}
    (route : BodyReturnRoute2 cond rv σ') :
    BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ' := by
  exact BigStepStmt.whileTrueReturn cond.hcondTrue route.hbody

theorem whileDivOfBodyDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyDivergesRoute2 cond) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact BigStepStmtDiv.whileBody cond.hcondTrue route.hbodyDiv

theorem whileDivOfConditionDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (route : ConditionDivergesRoute2 entry) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact route.whileDiv

end ExitLifting2

end WhileClosure2
end Cpp
