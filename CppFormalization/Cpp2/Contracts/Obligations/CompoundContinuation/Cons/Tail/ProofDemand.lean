import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Tail.Adequacy

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail proof demand

This is proof architecture, not a C++ runtime contract.  Once the head normal
route reaches the block tail, some proof principle must close that block tail.
-/

structure ProofDemand
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) : Type where
  close :
    BlockContinuationDynamicBoundary Γ σ1 tail →
      (∃ ctrl σ2, BigStepBlock σ1 tail ctrl σ2) ∨
        BigStepBlockDiv σ1 tail

structure Package
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) : Type where
  continuation : ContinuationInput route
  adequacy : AdequacyDemand route
  tailProof : ProofDemand route

namespace Package

/--
Cons tail adequacy is route-projected, not an extra programmer contract.
-/
def ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (continuation : ContinuationInput route)
    (tailProof : ProofDemand route) :
    Package route :=
  { continuation := continuation
    adequacy := AdequacyDemand.canonical route
    tailProof := tailProof }

def dynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (h : Package route) :
    BlockContinuationDynamicBoundary Γ σ1 tail :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (h : Package route) :
    (∃ ctrl σ2, BigStepBlock σ1 tail ctrl σ2) ∨
      BigStepBlockDiv σ1 tail :=
  h.tailProof.close h.dynamicBoundary

end Package

end Tail
end Cons
end CompoundContinuation
end Cpp
