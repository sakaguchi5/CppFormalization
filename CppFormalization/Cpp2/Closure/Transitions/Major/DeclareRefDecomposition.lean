import CppFormalization.Cpp2.Closure.Transitions.Minor.StateUpdateRoadmap
namespace Cpp


/-! =========================================================
    1. 環境側の分解
    ========================================================= -/

axiom typeFrameDeclObject_declareTypeRef_inv
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclObject (declareTypeRef Γ x τ) k y υ →
    typeFrameDeclObject Γ k y υ

axiom typeFrameDeclRef_declareTypeRef_cases
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclRef (declareTypeRef Γ x τ) k y υ →
    (k = 0 ∧ y = x ∧ υ = τ) ∨ typeFrameDeclRef Γ k y υ


/-! =========================================================
    2. 実現子の分解
    object は旧宣言の保全のみ。
    ref は旧宣言の保全 + 新 top ref の実現。
    ========================================================= -/

axiom declareRef_preserves_old_object_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ∀ {k y υ},
      typeFrameDeclObject Γ k y υ →
      ∃ b,
        runtimeFrameBindsObject σ' k y υ b ∧
        runtimeFrameOwnsAddress σ' k b ∧
        heapLiveTypedAt σ' b υ

axiom declareRef_preserves_old_ref_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ∀ {k y υ},
      typeFrameDeclRef Γ k y υ →
      ∃ b,
        runtimeFrameBindsRef σ' k y υ b ∧
        heapLiveTypedAt σ' b υ

axiom declareRef_realizes_new_top_ref
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    runtimeFrameBindsRef σ' 0 x τ a ∧
    heapLiveTypedAt σ' a τ


theorem declareRef_objectDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ∀ {k y υ},
      typeFrameDeclObject (declareTypeRef Γ x τ) k y υ →
      ∃ b,
        runtimeFrameBindsObject σ' k y υ b ∧
        runtimeFrameOwnsAddress σ' k b ∧
        heapLiveTypedAt σ' b υ := by
  intro hσ hdecl k y υ hty
  exact declareRef_preserves_old_object_realizers hσ hdecl
    (typeFrameDeclObject_declareTypeRef_inv hty)

theorem declareRef_refDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ∀ {k y υ},
      typeFrameDeclRef (declareTypeRef Γ x τ) k y υ →
      ∃ b,
        runtimeFrameBindsRef σ' k y υ b ∧
        heapLiveTypedAt σ' b υ := by
  intro hfresh hσ hdecl k y υ hty
  rcases typeFrameDeclRef_declareTypeRef_cases hfresh hty with hnew | hold
  · rcases hnew with ⟨hk, hy, hυ⟩
    subst hk; subst hy; subst hυ
    rcases declareRef_realizes_new_top_ref hσ hfresh hdecl with ⟨hbind, hlive⟩
    exact ⟨a, hbind, hlive⟩
  · exact declareRef_preserves_old_ref_realizers hσ hdecl hold


/-! =========================================================
    3. 構造 field の preservation
    ここは closeScope と同じく field ごとに分ける。
    ========================================================= -/

axiom declareRef_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    frameDepthAgreement (declareTypeRef Γ x τ) σ'

axiom declareRef_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    shadowingCompatible (declareTypeRef Γ x τ) σ'

axiom declareRef_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a0 σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ y υ, runtimeFrameBindsObject σ' k y υ a

axiom declareRef_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    refBindingsNeverOwned σ'

axiom declareRef_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    allObjectBindingsOwned σ'

axiom declareRef_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ownedAddressesNoDupPerFrame σ'

axiom declareRef_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ownedAddressesDisjointAcrossFrames σ'

axiom declareRef_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    allOwnedAddressesNamed σ'

axiom declareRef_preserves_initializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a0 σ' →
    ∀ {k y υ a},
      runtimeFrameBindsObject σ' k y υ a →
      heapInitializedTypedAt σ' a υ ∨ True

axiom declareRef_preserves_heapStoredValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a0 σ' →
    heapInitializedValuesTyped σ'

axiom declareRef_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    nextFreshAgainstOwned σ'

axiom declareRef_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a0 σ' →
    ∀ {k y υ a j},
      runtimeFrameBindsRef σ' k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a

/-! =========================================================
    4. 最終組み立て
    ========================================================= -/

theorem declareRef_concrete_state_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ' := by
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

  · exact declareRef_preserves_frameDepthAgreement hσ hfresh hdecl
  · exact declareRef_preserves_shadowingCompatible hσ hfresh hdecl
  · intro k y υ hty
    exact declareRef_objectDeclRealized_of_decomposition hσ hdecl hty
  · intro k y υ hty
    exact declareRef_refDeclRealized_of_decomposition hfresh hσ hdecl hty
  · intro k a hown
    exact declareRef_preserves_ownedAddressNamed hσ hdecl hown
  · exact declareRef_preserves_refBindingsNeverOwned hσ hdecl
  · exact declareRef_preserves_allObjectBindingsOwned hσ hdecl
  · exact declareRef_preserves_ownedNoDupPerFrame hσ hdecl
  · exact declareRef_preserves_ownedDisjointAcrossFrames hσ hdecl
  · exact declareRef_preserves_allOwnedAddressesNamed hσ hdecl
  · exact declareRef_preserves_heapStoredValuesTyped hσ hdecl
  · intro k y υ a hbind
    exact declareRef_preserves_initializedValuesTyped hσ hdecl hbind
  · exact declareRef_preserves_nextFreshAgainstOwned hσ hdecl
  · intro k y υ a j hbind hjk
    exact declareRef_preserves_refTargetsAvoidInnerOwned hσ hfresh hdecl hbind hjk

theorem declares_ref_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ' := by
  intro hfresh hσ hdecl
  exact declareRef_concrete_state_of_decomposition hfresh hσ hdecl

end Cpp
