import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Route

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail static/adequacy projection

Tail static/adequacy is a continuation payload attached to a core route; it is
not part of the core route itself and not a programmer-side replay contract.

The legacy full `SeqHeadNormalRouteCI` still bundles this payload, so this file
also provides an adapter from the legacy full route to the standalone demand.
-/

structure AdequacyDemand
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Type where
  static : BodyStaticBoundaryCI route.Θ t
  tailAdequacy : BodyAdequacyCI route.Θ σ1 t static.profile

namespace AdequacyDemand

/--
Materialize the standalone tail adequacy demand from the legacy full route.

This is a compatibility adapter: new code should pass the demand separately or
derive it from lower adequacy/proof infrastructure, not treat it as part of the
actual route.
-/
noncomputable def ofLegacy
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    AdequacyDemand route.toCore :=
  { static := route.tail.static
    tailAdequacy := route.tail.support.toBodyAdequacyCI }

end AdequacyDemand

end Tail
end Seq
end CompoundContinuation
end Cpp
