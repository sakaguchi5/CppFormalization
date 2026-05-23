import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Tail.Continuation

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail static/adequacy projection
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
The selected cons head-normal route already carries the block-tail adequacy
payload, so this is not an additional programmer-side contract.
-/
def canonical
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) :
    AdequacyDemand route :=
  { tailAdequacy := adequacy route }

end AdequacyDemand


end Tail
end Cons
end CompoundContinuation
end Cpp
