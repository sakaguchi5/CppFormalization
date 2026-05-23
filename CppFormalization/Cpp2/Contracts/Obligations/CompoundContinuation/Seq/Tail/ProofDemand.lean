import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Tail.Continuation

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail proof demand

This is proof architecture, not a C++ runtime contract.  Once the selected left
normal core route reaches the tail statement, some proof principle must close
that tail.

Tail adequacy is deliberately not a field of `Package`; it is a separate
profile/semantic obligation, not needed for dynamic tail lifting.
-/

structure ProofDemand
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Type where
  close :
    StmtContinuationDynamicBoundary route.Θ σ1 t →
      (∃ ctrl σ2, BigStepStmt σ1 t ctrl σ2) ∨
        BigStepStmtDiv σ1 t

structure Package
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Type where
  continuation : ContinuationInput route
  tailProof : ProofDemand route

namespace Package

def ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (continuation : ContinuationInput route)
    (tailProof : ProofDemand route) :
    Package route :=
  { continuation := continuation
    tailProof := tailProof }

def dynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : Package route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : Package route) :
    (∃ ctrl σ2, BigStepStmt σ1 t ctrl σ2) ∨
      BigStepStmtDiv σ1 t :=
  h.tailProof.close h.dynamicBoundary

end Package

end Tail
end Seq
end CompoundContinuation
end Cpp
