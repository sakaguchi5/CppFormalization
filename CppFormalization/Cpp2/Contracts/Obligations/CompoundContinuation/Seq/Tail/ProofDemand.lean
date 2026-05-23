import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Tail.Adequacy

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail proof demand

This is proof architecture, not a C++ runtime contract.  Once the selected left
normal route reaches the tail statement, some proof principle must close that
tail.
-/

structure ProofDemand
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  close :
    StmtContinuationDynamicBoundary route.Θ σ1 t →
      (∃ ctrl σ2, BigStepStmt σ1 t ctrl σ2) ∨
        BigStepStmtDiv σ1 t

structure Package
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  continuation : ContinuationInput route
  adequacy : AdequacyDemand route
  tailProof : ProofDemand route

namespace Package

/--
Seq tail adequacy is route-projected, not an extra programmer contract.
This constructor keeps package construction focused on the genuine dynamic
continuation input and the proof demand.
-/
noncomputable def ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (continuation : ContinuationInput route)
    (tailProof : ProofDemand route) :
    Package route :=
  { continuation := continuation
    adequacy := AdequacyDemand.canonical route
    tailProof := tailProof }

def dynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : Package route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  h.continuation.toDynamicBoundary

def closeTail
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : Package route) :
    (∃ ctrl σ2, BigStepStmt σ1 t ctrl σ2) ∨
      BigStepStmtDiv σ1 t :=
  h.tailProof.close h.dynamicBoundary

end Package

end Tail
end Seq
end CompoundContinuation
end Cpp
