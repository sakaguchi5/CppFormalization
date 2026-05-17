import CppFormalization.Cpp2.Effects.ReadinessTransportEffect

namespace Cpp
namespace Contracts
namespace Certified

abbrev PlaceReadyCertifiedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  PlaceReadyTransportByEffect eff

abbrev ExprReadyCertifiedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  ExprReadyTransportByEffect eff

abbrev StmtReadyCertifiedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  StmtReadyTransportByEffect eff

abbrev BlockReadyCertifiedByEffect
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Prop :=
  BlockReadyTransportByEffect eff

abbrev ReadinessTransportCertifiedPackage
    {Γ Δ : TypeEnv} {σ σ' : State} {head : CppStmt}
    (eff : NormalHeadEffect Γ Δ σ σ' head) : Type :=
  ReadinessTransportEffectPackage eff

end Certified
end Contracts
end Cpp
