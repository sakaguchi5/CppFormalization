import CppFormalization.Cpp2.Continuation.Compound.While.Tail.Adequacy

namespace Cpp
namespace CompoundContinuation
namespace While
namespace Tail

/-!
# While tail proof demand

This is proof architecture, not a C++ runtime contract.
-/

structure WhileTailProofDemand
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  close :
    StmtContinuationDynamicBoundary Γ σ (.whileStmt c body) →
      (∃ ctrl σ2, BigStepStmt σ (.whileStmt c body) ctrl σ2) ∨
        BigStepStmtDiv σ (.whileStmt c body)

structure NormalProofDemand
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyNormalRoute cond σ1) : Type where
  demand : WhileTailProofDemand Γ σ1 c body

structure ContinueProofDemand
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyContinueRoute cond σ1) : Type where
  demand : WhileTailProofDemand Γ σ1 c body

structure NormalPackage
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyNormalRoute cond σ1) : Type where
  continuation : Backedge.NormalContinuationInput route
  adequacy : NormalAdequacyDemand route
  tailProof : NormalProofDemand route

structure ContinuePackage
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    (route : BodyContinueRoute cond σ1) : Type where
  continuation : Backedge.ContinueContinuationInput route
  adequacy : ContinueAdequacyDemand route
  tailProof : ContinueProofDemand route

namespace NormalPackage

def dynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (h : NormalPackage route) :
    StmtContinuationDynamicBoundary Γ σ1 (.whileStmt c body) :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyNormalRoute cond σ1}
    (h : NormalPackage route) :
    (∃ ctrl σ2, BigStepStmt σ1 (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ1 (.whileStmt c body) :=
  h.tailProof.demand.close h.dynamicBoundary

end NormalPackage

namespace ContinuePackage

def dynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (h : ContinuePackage route) :
    StmtContinuationDynamicBoundary Γ σ1 (.whileStmt c body) :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    {entry : Entry Γ σ c body}
    {cond : ConditionTrueRoute entry}
    {route : BodyContinueRoute cond σ1}
    (h : ContinuePackage route) :
    (∃ ctrl σ2, BigStepStmt σ1 (.whileStmt c body) ctrl σ2) ∨
      BigStepStmtDiv σ1 (.whileStmt c body) :=
  h.tailProof.demand.close h.dynamicBoundary

end ContinuePackage

end Tail
end While
end CompoundContinuation
end Cpp
