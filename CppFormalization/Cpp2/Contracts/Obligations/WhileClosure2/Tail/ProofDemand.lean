import CppFormalization.Cpp2.Contracts.Obligations.WhileClosure2.Tail.Adequacy

namespace Cpp
namespace WhileClosure2

/-!
# Tail proof demand

This is proof architecture, not a C++ runtime contract.  A body-normal or
body-continue route reaches the same while statement at a new state; some proof
principle must close that tail.
-/

/-- Closure/progress-or-divergence demand for the same while at a post-state. -/
structure WhileTailProofDemand2
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  close :
    StmtContinuationDynamicBoundary Γ σ (.whileStmt c body) →
      (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
        BigStepStmtDiv σ (.whileStmt c body)

structure NormalTailProofDemand2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  demand : WhileTailProofDemand2 Γ σ' c body

structure ContinueTailProofDemand2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  demand : WhileTailProofDemand2 Γ σ' c body

/--
Package needed after a normal body step: continuation input gives a dynamic
boundary, adequacy explains the tail profile, and proof demand closes the same
while.
-/
structure NormalTailPackage2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyNormalRoute2 cond σ') : Type where
  continuation : NormalBackedgeContinuationInput2 route
  adequacy : NormalTailAdequacyDemand2 route
  tailProof : NormalTailProofDemand2 route

/--
Package needed after a continue body step: continuation input gives a dynamic
boundary, adequacy explains the tail profile, and proof demand closes the same
while.
-/
structure ContinueTailPackage2
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    (route : BodyContinueRoute2 cond σ') : Type where
  continuation : ContinueBackedgeContinuationInput2 route
  adequacy : ContinueTailAdequacyDemand2 route
  tailProof : ContinueTailProofDemand2 route

namespace NormalTailPackage2

def dynamicBoundary
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalTailPackage2 route) :
    StmtContinuationDynamicBoundary Γ σ' (.whileStmt c body) :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyNormalRoute2 cond σ'}
    (h : NormalTailPackage2 route) :
    (∃ ctrl σ2, BigStepStmt σ' (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ' (.whileStmt c body) :=
  h.tailProof.demand.close h.dynamicBoundary

end NormalTailPackage2

namespace ContinueTailPackage2

def dynamicBoundary
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueTailPackage2 route) :
    StmtContinuationDynamicBoundary Γ σ' (.whileStmt c body) :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    {entry : WhileEntry2 Γ σ c body}
    {cond : ConditionTrueRoute2 entry}
    {route : BodyContinueRoute2 cond σ'}
    (h : ContinueTailPackage2 route) :
    (∃ ctrl σ2, BigStepStmt σ' (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ' (.whileStmt c body) :=
  h.tailProof.demand.close h.dynamicBoundary

end ContinueTailPackage2

end WhileClosure2
end Cpp
