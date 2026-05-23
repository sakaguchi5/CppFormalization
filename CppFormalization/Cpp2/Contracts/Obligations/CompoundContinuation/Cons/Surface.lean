import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Progress.HeadLocal
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Tail.Lifting
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Exit.Lifting

namespace Cpp
namespace CompoundContinuation
namespace Cons

/-!
# Cons surface

Cons is the statement-to-block-tail instance of the compound-continuation
pattern.
-/

structure TailSurface
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) : Type where
  continuation : Tail.ContinuationInput route
  adequacy : Tail.AdequacyDemand route
  proof : Tail.ProofDemand route

/--
Surface constructor with the route-projected adequacy filled in canonically.
-/
def TailSurface.ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (continuation : Tail.ContinuationInput route)
    (proof : Tail.ProofDemand route) :
    TailSurface route :=
  { continuation := continuation
    adequacy := Tail.AdequacyDemand.canonical route
    proof := proof }


def TailSurface.toPackage
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (h : TailSurface route) :
    Tail.Package route :=
  { continuation := h.continuation
    adequacy := h.adequacy
    tailProof := h.proof }

end Cons
end CompoundContinuation
end Cpp
