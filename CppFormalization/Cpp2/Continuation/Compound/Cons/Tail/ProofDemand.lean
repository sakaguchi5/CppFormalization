import CppFormalization.Cpp2.Continuation.Compound.Cons.Tail.Continuation

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail proof demand

This is proof architecture, not a C++ runtime contract.  Once the head-normal
core route reaches the block tail, some proof principle must close that block
tail.
-/

structure ProofDemand
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Type where
  close :
    BlockContinuationDynamicBoundary Γ σ1 tail →
      (∃ ctrl σ2, BigStepBlock σ1 tail ctrl σ2) ∨
        BigStepBlockDiv σ1 tail

structure Package
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Type where
  continuation : ContinuationInput route
  tailProof : ProofDemand route

namespace Package

/--
Cons tail package construction no longer asks for tail adequacy.  Adequacy is a
separate projection from the legacy full route when such a route is available.
-/
def ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (continuation : ContinuationInput route)
    (tailProof : ProofDemand route) :
    Package route :=
  { continuation := continuation
    tailProof := tailProof }

def dynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : Package route) :
    BlockContinuationDynamicBoundary Γ σ1 tail :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : Package route) :
    (∃ ctrl σ2, BigStepBlock σ1 tail ctrl σ2) ∨
      BigStepBlockDiv σ1 tail :=
  h.tailProof.close h.dynamicBoundary

end Package

end Tail
end Cons
end CompoundContinuation
end Cpp
