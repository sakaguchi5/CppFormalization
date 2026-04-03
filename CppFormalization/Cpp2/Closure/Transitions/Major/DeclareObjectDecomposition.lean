import CppFormalization.Cpp2.Closure.Transitions.Major.CloseScopeDecomposition

namespace Cpp

/-!
# Closure.Transitions.Major.DeclareObjectDecomposition

`declareObject` は `declareRef` より一段重い。
理由は、新しい top object binding だけでなく、top ownership と fresh address を実際に増やすからである。

このファイルでは、`DeclaresObject` が `ScopedTypedStateConcrete` を保つことを、
`closeScope` と同じく field ごとに分解して組み立てる。
-/

/-! =========================================================
    1. 型環境側の分解
    ========================================================= -/

axiom typeFrameDeclRef_declareTypeObject_inv
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclRef (declareTypeObject Γ x τ) k y υ →
    typeFrameDeclRef Γ k y υ

axiom typeFrameDeclObject_declareTypeObject_cases
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclObject (declareTypeObject Γ x τ) k y υ →
    (k = 0 ∧ y = x ∧ υ = τ) ∨ typeFrameDeclObject Γ k y υ


/-! =========================================================
    2. 実現子の分解
    object は「新しい top object」か「旧 object 実現の保全」。
    ref は新規ケースなしで、旧 ref 実現の保全のみ。
    ========================================================= -/

axiom declareObject_preserves_old_object_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclObject Γ k y υ →
      ∃ a,
        runtimeFrameBindsObject σ' k y υ a ∧
        runtimeFrameOwnsAddress σ' k a ∧
        heapLiveTypedAt σ' a υ

axiom declareObject_preserves_old_ref_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclRef Γ k y υ →
      ∃ a,
        runtimeFrameBindsRef σ' k y υ a ∧
        heapLiveTypedAt σ' a υ

axiom declareObject_realizes_new_top_object
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∃ a,
      runtimeFrameBindsObject σ' 0 x τ a ∧
      runtimeFrameOwnsAddress σ' 0 a ∧
      heapLiveTypedAt σ' a τ


theorem declareObject_objectDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclObject (declareTypeObject Γ x τ) k y υ →
      ∃ a,
        runtimeFrameBindsObject σ' k y υ a ∧
        runtimeFrameOwnsAddress σ' k a ∧
        heapLiveTypedAt σ' a υ := by
  intro hfresh hσ hdecl k y υ hty
  rcases typeFrameDeclObject_declareTypeObject_cases hfresh hty with hnew | hold
  · rcases hnew with ⟨hk, hy, hυ⟩
    subst hk
    subst hy
    subst hυ
    exact declareObject_realizes_new_top_object hσ hfresh hdecl
  · exact declareObject_preserves_old_object_realizers hσ hfresh hdecl hold


theorem declareObject_refDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclRef (declareTypeObject Γ x τ) k y υ →
      ∃ a,
        runtimeFrameBindsRef σ' k y υ a ∧
        heapLiveTypedAt σ' a υ := by
  intro hfresh hσ hdecl k y υ hty
  exact declareObject_preserves_old_ref_realizers hσ hfresh hdecl
    (typeFrameDeclRef_declareTypeObject_inv hty)


/-! =========================================================
    3. 構造 field の preservation
    ========================================================= -/

axiom declareObject_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    frameDepthAgreement (declareTypeObject Γ x τ) σ'

axiom declareObject_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    shadowingCompatible (declareTypeObject Γ x τ) σ'

axiom declareObject_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ y υ, runtimeFrameBindsObject σ' k y υ a

axiom declareObject_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    refBindingsNeverOwned σ'

axiom declareObject_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    allObjectBindingsOwned σ'

axiom declareObject_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ownedAddressesNoDupPerFrame σ'

axiom declareObject_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ownedAddressesDisjointAcrossFrames σ'

axiom declareObject_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    allOwnedAddressesNamed σ'

axiom declareObject_preserves_initializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a},
      runtimeFrameBindsObject σ' k y υ a →
      heapInitializedTypedAt σ' a υ ∨ True

axiom declareObject_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    nextFreshAgainstOwned σ'

axiom declareObject_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a j},
      runtimeFrameBindsRef σ' k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a

/-- オブジェクト宣言はヒープ全体の型整合性を保存する -/
axiom declareObject_preserves_heapInitializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    heapInitializedValuesTyped σ'
/-! =========================================================
    4. 最終組み立て
    ========================================================= -/


theorem declareObject_concrete_state_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ' := by
  intro hfresh hσ hdecl
  refine
    { frameDepth := ?_
      shadowing := ?_
      objectDeclRealized := ?_
      refDeclRealized := ?_
      ownedAddressNamed := ?_
      refsNotOwned := ?_
      objectsOwned := ?_
      ownedNoDupPerFrame := ?_
      ownedDisjoint := ?_
      ownedNamed := ?_
      initializedValuesTyped := ?_
      heapStoredValuesTyped := ?_
      nextFresh := ?_
      refTargetsAvoidInnerOwned := ?_ }

  · exact declareObject_preserves_frameDepthAgreement hσ hfresh hdecl
  · exact declareObject_preserves_shadowingCompatible hσ hfresh hdecl
  · intro k y υ hty
    exact declareObject_objectDeclRealized_of_decomposition hfresh hσ hdecl hty
  · intro k y υ hty
    exact declareObject_refDeclRealized_of_decomposition hfresh hσ hdecl hty
  · intro k a hown
    exact declareObject_preserves_ownedAddressNamed hσ hfresh hdecl hown
  · exact declareObject_preserves_refBindingsNeverOwned hσ hfresh hdecl
  · exact declareObject_preserves_allObjectBindingsOwned hσ hfresh hdecl
  · exact declareObject_preserves_ownedNoDupPerFrame hσ hfresh hdecl
  · exact declareObject_preserves_ownedDisjointAcrossFrames hσ hfresh hdecl
  · exact declareObject_preserves_allOwnedAddressesNamed hσ hfresh hdecl
  · exact declareObject_preserves_heapInitializedValuesTyped hσ hfresh hdecl
  · intro k y τ_obj addr hbind
    exact declareObject_preserves_initializedValuesTyped hσ hfresh hdecl hbind
  · exact declareObject_preserves_nextFreshAgainstOwned hσ hfresh hdecl
  · intro k y υ a j hbind hjk
    exact declareObject_preserves_refTargetsAvoidInnerOwned hσ hfresh hdecl hbind hjk


theorem declares_object_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ' := by
  intro hfresh hσ hdecl
  exact declareObject_concrete_state_of_decomposition hfresh hσ hdecl

end Cpp
