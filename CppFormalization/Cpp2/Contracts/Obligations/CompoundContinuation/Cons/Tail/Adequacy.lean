import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Route

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail static/adequacy projection

Tail adequacy is kept as a standalone legacy-full-route projection.  It is not
part of the mainline continuation/lifting package, whose route is only
`HeadNormalRouteCore`.
-/

def static
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) :
    BlockBodyStaticBoundaryCI Γ tail :=
  route.tailPayload.static

def adequacy
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) :
    BlockBodyAdequacyCI Γ σ1 tail (static route).profile :=
  route.tailPayload.adequacy

structure AdequacyDemand
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) : Type where
  tailAdequacy : BlockBodyAdequacyCI Γ σ1 tail (static route).profile := adequacy route

namespace AdequacyDemand

/--
The legacy full route already carries the block-tail adequacy payload, so this
is not an additional programmer-side contract.
-/
def canonical
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) :
    AdequacyDemand route :=
  { tailAdequacy := adequacy route }

/-- Compatibility spelling emphasizing that the source is the legacy full route. -/
def ofLegacy
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) :
    AdequacyDemand route :=
  canonical route

end AdequacyDemand

end Tail
end Cons
end CompoundContinuation
end Cpp
