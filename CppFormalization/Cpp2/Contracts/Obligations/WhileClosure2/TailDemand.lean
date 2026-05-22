import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.TailAdequacy

namespace Cpp
namespace WhileClosure2

/-!
# Tail recursion/divergence demand

This is proof architecture, not a C++ runtime contract.  A body-normal or
body-continue route reaches the same while statement at a new state; some proof
principle must close that tail.
-/

/-- Closure/progress-or-divergence demand for the same while at a post-state. -/
structure WhileTailDemand2
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  close :
    StmtContinuationDynamicBoundary Γ σ (.whileStmt c body) →
      (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
        BigStepStmtDiv σ (.whileStmt c body)

structure NormalTailDemand2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  demand : WhileTailDemand2 Γ σ' c body

structure ContinueTailDemand2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  demand : WhileTailDemand2 Γ σ' c body

/--
Package needed after a normal body step: replay gives a dynamic boundary,
adequacy explains the tail profile, and demand closes the same while.
-/
structure NormalTailPackage2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  replay : NormalBackedgeReplay2 route
  adequacy : NormalTailAdequacyDemand2 route
  tail : NormalTailDemand2 route

/--
Package needed after a continue body step: replay gives a dynamic boundary,
adequacy explains the tail profile, and demand closes the same while.
-/
structure ContinueTailPackage2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  replay : ContinueBackedgeReplay2 route
  adequacy : ContinueTailAdequacyDemand2 route
  tail : ContinueTailDemand2 route

end WhileClosure2
end Cpp
