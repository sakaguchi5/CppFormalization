import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectRealizers
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectOwnership
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext

namespace Cpp

axiom declareObject_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ → currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' → objectBindingSound σ'

axiom declareObject_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ → currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' → refBindingSound σ'

axiom declares_object_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x → ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' → ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ'
end Cpp
