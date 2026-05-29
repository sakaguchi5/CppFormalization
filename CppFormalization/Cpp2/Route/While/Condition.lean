import CppFormalization.Cpp2.Continuation.Compound.While.Entry

namespace Cpp
namespace CompoundContinuation
namespace While

/-!
# Condition-first routes
-/

structure ConditionTrueRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (entry : Entry Γ σ c body) : Type where
  hcondTrue : BigStepValue σ c (.bool true)

structure ConditionFalseRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (entry : Entry Γ σ c body) : Type where
  hcondFalse : BigStepValue σ c (.bool false)

/--
The current semantics has statement divergence but no separate expression
divergence object.  Therefore this route stores the already lifted while
divergence fact.
-/
structure ConditionDivergesRoute
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (entry : Entry Γ σ c body) : Type where
  whileDiv : BigStepStmtDiv σ (.whileStmt c body)

end While
end CompoundContinuation
end Cpp
