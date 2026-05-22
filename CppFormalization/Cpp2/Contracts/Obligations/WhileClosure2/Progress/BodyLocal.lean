import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Route.Body

namespace Cpp
namespace WhileClosure2

/-!
# Body-local progress demand

This is proof architecture, not a C++ replay contract.  Under a true condition,
the loop body must be classified as one of the local outcomes that the while
semantics understands.
-/

inductive BodyLocalOutcome2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (cond : ConditionTrueRoute2 entry) : Type where
  | normal (σ' : State) :
      BodyNormalRoute2 cond σ' →
      BodyLocalOutcome2 cond
  | continue (σ' : State) :
      BodyContinueRoute2 cond σ' →
      BodyLocalOutcome2 cond
  | break (σ' : State) :
      BodyBreakRoute2 cond σ' →
      BodyLocalOutcome2 cond
  | return (rv : Option Value) (σ' : State) :
      BodyReturnRoute2 cond rv σ' →
      BodyLocalOutcome2 cond
  | diverges :
      BodyDivergesRoute2 cond →
      BodyLocalOutcome2 cond

/-- Local progress/divergence package for the body under a true condition. -/
structure BodyLocalProgress2
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    (cond : ConditionTrueRoute2 entry) : Type where
  outcome : BodyLocalOutcome2 cond

end WhileClosure2
end Cpp
