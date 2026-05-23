import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Tail.Lifting
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Exit.Lifting

namespace Cpp
namespace CompoundContinuation
namespace Seq

/-!
# Seq surface

Seq is the statement-to-statement instance of the compound-continuation pattern.
-/

structure TailSurface
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  continuation : Tail.ContinuationInput route
  adequacy : Tail.AdequacyDemand route
  proof : Tail.ProofDemand route

/--
Surface constructor with the route-projected adequacy filled in canonically.
-/
noncomputable def TailSurface.ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (continuation : Tail.ContinuationInput route)
    (proof : Tail.ProofDemand route) :
    TailSurface route :=
  { continuation := continuation
    adequacy := Tail.AdequacyDemand.canonical route
    proof := proof }


def TailSurface.toPackage
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : TailSurface route) :
    Tail.Package route :=
  { continuation := h.continuation
    adequacy := h.adequacy
    tailProof := h.proof }

end Seq
end CompoundContinuation
end Cpp
