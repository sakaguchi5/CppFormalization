import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.While.Route.Body

namespace Cpp
namespace CompoundContinuation
namespace While
namespace Exit

/-!
# While non-tail exit lifting
-/

theorem stepOfConditionFalse
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (route : ConditionFalseRoute entry) :
    BigStepStmt σ (.whileStmt c body) .normal σ := by
  exact BigStepStmt.whileFalse route.hcondFalse

theorem stepOfBodyBreak
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyBreakRoute cond σ1) :
    BigStepStmt σ (.whileStmt c body) .normal σ1 := by
  exact BigStepStmt.whileTrueBreak cond.hcondTrue route.hbody

theorem stepOfBodyReturn
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {rv : Option Value}
    (route : BodyReturnRoute cond rv σ1) :
    BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ1 := by
  exact BigStepStmt.whileTrueReturn cond.hcondTrue route.hbody

theorem divOfBodyDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyDivergesRoute cond) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact BigStepStmtDiv.whileBody cond.hcondTrue route.hbodyDiv

theorem divOfConditionDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (route : ConditionDivergesRoute entry) :
    BigStepStmtDiv σ (.whileStmt c body) := by
  exact route.whileDiv

end Exit
end While
end CompoundContinuation
end Cpp
