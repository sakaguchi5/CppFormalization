import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Entry

namespace Cpp
namespace WhileClosure2

/-!
# Condition routes

A clean while proof starts by routing the condition.  Body results should only be
considered under the true route.
-/

/-- The condition evaluates to true, so the body is executed. -/
structure ConditionTrueRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (entry : WhileEntry2 Γ σ c body) : Type where
  hcondTrue : BigStepValue σ c (.bool true)

/-- The condition evaluates to false, so the while exits normally. -/
structure ConditionFalseRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (entry : WhileEntry2 Γ σ c body) : Type where
  hcondFalse : BigStepValue σ c (.bool false)

/--
Condition-divergence route.

The first scaffold stores the already lifted while divergence fact rather than
guessing the exact expression-divergence primitive name.  A later refinement can
replace this by a smaller condition-divergence witness plus a lifting theorem.
-/
structure ConditionDivergesRoute2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (entry : WhileEntry2 Γ σ c body) : Type where
  whileDiv : BigStepStmtDiv σ (.whileStmt c body)

end WhileClosure2
end Cpp
