import CppFormalization.Cpp2.Effects.ReadinessTransportEffect

namespace Cpp
namespace Contracts
namespace Certified

theorem declareObjFreshObjectPlaceReady
    {Γ Δ : TypeEnv} {σ' : State} {τ : CppType} {x : Ident}
    (hname : DeclareObjNameEffect Γ Δ τ x)
    (hpost : ScopedTypedStateConcrete Δ σ') :
    PlaceReadyConcrete Δ σ' (.var x) τ :=
  Cpp.declareObj_effect_fresh_object_place_ready hname hpost

theorem declareRefFreshPlaceReady
    {Γ Δ : TypeEnv} {σ' : State} {τ : CppType} {x : Ident} {p0 : PlaceExpr}
    (hname : DeclareRefNameEffect Γ Δ τ x p0)
    (hpost : ScopedTypedStateConcrete Δ σ') :
    PlaceReadyConcrete Δ σ' (.var x) τ :=
  Cpp.declareRef_effect_fresh_place_ready hname hpost

end Certified
end Contracts
end Cpp
