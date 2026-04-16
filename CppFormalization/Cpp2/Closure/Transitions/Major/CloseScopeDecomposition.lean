import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp
axiom closeScope_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ → CloseScope σ σ' → objectBindingSound σ'

axiom closeScope_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ → CloseScope σ σ' → refBindingSound σ'

axiom closeScope_preserves_concrete_state_via_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ → CloseScope σ σ' → ScopedTypedStateConcrete Γ σ'
end Cpp
