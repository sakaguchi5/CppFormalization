import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.BodyRoute

namespace Cpp
namespace WhileClosure2

/-!
# Exit lifting

This file names the semantic lifting layer separately from backedge replay.

In the first clean-room scaffold, the lifted while step/divergence is stored as
a field.  This avoids baking in old while-provider imports or relying on exact
constructor names for every semantic rule.  Later files can replace these fields
by theorem-backed constructors.
-/

structure FalseExit2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (route : ConditionFalseRoute2 entry) : Type where
  whileStep : BigStepStmt σ (.whileStmt c body) .normal σ

structure BreakExit2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyBreakRoute2 cond σ') : Type where
  whileStep : BigStepStmt σ (.whileStmt c body) .normal σ'

structure ReturnExit2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {rv : Option Value}
    (route : BodyReturnRoute2 cond rv σ') : Type where
  whileStep : BigStepStmt σ (.whileStmt c body) (.returnResult rv) σ'

structure BodyDivergesExit2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyDivergesRoute2 cond) : Type where
  whileDiv : BigStepStmtDiv σ (.whileStmt c body)

structure ConditionDivergesExit2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (route : ConditionDivergesRoute2 entry) : Type where
  whileDiv : BigStepStmtDiv σ (.whileStmt c body) := route.whileDiv

end WhileClosure2
end Cpp
