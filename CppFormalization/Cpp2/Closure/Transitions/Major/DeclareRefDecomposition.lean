import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp
axiom declareRef_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ → currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' → objectBindingSound σ'

axiom declareRef_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ → currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' → refBindingSound σ'

axiom declares_ref_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {a : Nat} :
    currentTypeScopeFresh Γ x → ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' → ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ'
end Cpp
