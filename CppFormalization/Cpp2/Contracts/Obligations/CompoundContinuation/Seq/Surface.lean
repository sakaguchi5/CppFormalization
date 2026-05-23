import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Tail.Lifting
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Exit.Lifting

namespace Cpp
namespace CompoundContinuation
namespace Seq

/-!
# Seq surface

Seq is the statement-to-statement instance of the compound-continuation pattern.

This surface is now core-route based.  It contains only the dynamic continuation
input and the proof demand needed to close/lift the tail.  Tail adequacy is a
separate profile/semantic obligation, not part of this dynamic surface.
-/

structure TailSurface
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Type where
  continuation : Tail.ContinuationInput route
  proof : Tail.ProofDemand route

def TailSurface.ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (continuation : Tail.ContinuationInput route)
    (proof : Tail.ProofDemand route) :
    TailSurface route :=
  { continuation := continuation
    proof := proof }

def TailSurface.toPackage
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : TailSurface route) :
    Tail.Package route :=
  { continuation := h.continuation
    tailProof := h.proof }

end Seq
end CompoundContinuation
end Cpp
