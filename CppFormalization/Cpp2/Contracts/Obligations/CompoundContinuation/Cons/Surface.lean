import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Progress.HeadLocal
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Tail.Lifting
import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Exit.Lifting

namespace Cpp
namespace CompoundContinuation
namespace Cons

/-!
# Cons surface

Cons is the statement-to-block-tail instance of the compound-continuation
pattern.  The tail surface is now indexed by the head-normal route core; tail
static/adequacy is no longer part of the mainline surface package.
-/

structure TailSurface
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRouteCore Γ σ σ1 head tail) : Type where
  continuation : Tail.ContinuationInput route
  proof : Tail.ProofDemand route

/-- Surface constructor focused on the genuine continuation input and proof demand. -/
def TailSurface.ofContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (continuation : Tail.ContinuationInput route)
    (proof : Tail.ProofDemand route) :
    TailSurface route :=
  { continuation := continuation
    proof := proof }


def TailSurface.toPackage
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRouteCore Γ σ σ1 head tail}
    (h : TailSurface route) :
    Tail.Package route :=
  { continuation := h.continuation
    tailProof := h.proof }

/-- Compatibility helper for callers that still carry the legacy full route. -/
def TailSurface.ofLegacyContinuationAndProof
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (continuation : Tail.ContinuationInput route.toCore)
    (proof : Tail.ProofDemand route.toCore) :
    TailSurface route.toCore :=
  TailSurface.ofContinuationAndProof continuation proof

end Cons
end CompoundContinuation
end Cpp
