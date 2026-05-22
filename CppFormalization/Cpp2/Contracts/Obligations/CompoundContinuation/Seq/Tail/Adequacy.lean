import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Tail.Continuation

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail static/adequacy projection

The selected seq route already carries the tail static boundary and adequacy
payload.  This file exposes those projections under the shared continuation
naming scheme.
-/

def static
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    BodyStaticBoundaryCI route.Θ t :=
  route.tail.static

noncomputable def adequacy
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    BodyAdequacyCI route.Θ σ1 t (static route).profile :=
  route.tail.support.toBodyAdequacyCI

structure AdequacyDemand
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  tailAdequacy : BodyAdequacyCI route.Θ σ1 t (static route).profile := adequacy route

end Tail
end Seq
end CompoundContinuation
end Cpp
