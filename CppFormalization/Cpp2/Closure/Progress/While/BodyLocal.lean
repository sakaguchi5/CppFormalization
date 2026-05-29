import CppFormalization.Cpp2.Route.While.Body

namespace Cpp
namespace CompoundContinuation
namespace While

/-!
# Body-local progress demand

This is proof architecture, not a C++ replay contract.
-/

inductive BodyLocalOutcome
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (cond : ConditionTrueRoute entry) : Type where
  | normal (σ1 : State) :
      BodyNormalRoute cond σ1 →
      BodyLocalOutcome cond
  | continued (σ1 : State) :
      BodyContinueRoute cond σ1 →
      BodyLocalOutcome cond
  | broke (σ1 : State) :
      BodyBreakRoute cond σ1 →
      BodyLocalOutcome cond
  | returned (rv : Option Value) (σ1 : State) :
      BodyReturnRoute cond rv σ1 →
      BodyLocalOutcome cond
  | diverged :
      BodyDivergesRoute cond →
      BodyLocalOutcome cond

structure BodyLocalProgress
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    (cond : ConditionTrueRoute entry) : Type where
  outcome : BodyLocalOutcome cond

end While
end CompoundContinuation
end Cpp
