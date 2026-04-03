import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
`OpenScope` は top に空 frame を 1 枚積むだけで、
既存の binding / ownership / heap live は壊さない。
したがって preservation の本体は、
- type env 側の宣言が 1 段 shift すること
- runtime 側の realizers も 1 段 shift して残ること
- ownership / freshness / shadowing が保たれること
の分解になる。
-/

/- =========================================================
   1. 環境側の分解
   pushTypeScope の top frame は空なので、
   decl はすべて 1 段下の旧環境から来る。
   ========================================================= -/

axiom typeFrameDeclObject_pushTypeScope_cases
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclObject (pushTypeScope Γ) k x τ →
    ∃ j, k = j + 1 ∧ typeFrameDeclObject Γ j x τ

axiom typeFrameDeclRef_pushTypeScope_cases
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclRef (pushTypeScope Γ) k x τ →
    ∃ j, k = j + 1 ∧ typeFrameDeclRef Γ j x τ


/- =========================================================
   2. realizers の preservation
   旧 realizers が 1 段 shift して残る。
   ========================================================= -/

axiom openScope_preserves_shifted_object_realizers
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclObject Γ k x τ →
      ∃ a,
        runtimeFrameBindsObject σ' (k + 1) x τ a ∧
        runtimeFrameOwnsAddress σ' (k + 1) a ∧
        heapLiveTypedAt σ' a τ

axiom openScope_preserves_shifted_ref_realizers
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclRef Γ k x τ →
      ∃ a,
        runtimeFrameBindsRef σ' (k + 1) x τ a ∧
        heapLiveTypedAt σ' a τ


theorem openScope_objectDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclObject (pushTypeScope Γ) k x τ →
      ∃ a,
        runtimeFrameBindsObject σ' k x τ a ∧
        runtimeFrameOwnsAddress σ' k a ∧
        heapLiveTypedAt σ' a τ := by
  intro hσ hopen k x τ hdecl
  rcases typeFrameDeclObject_pushTypeScope_cases hdecl with ⟨j, hk, hdeclOld⟩
  subst hk
  exact openScope_preserves_shifted_object_realizers hσ hopen hdeclOld

theorem openScope_refDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclRef (pushTypeScope Γ) k x τ →
      ∃ a,
        runtimeFrameBindsRef σ' k x τ a ∧
        heapLiveTypedAt σ' a τ := by
  intro hσ hopen k x τ hdecl
  rcases typeFrameDeclRef_pushTypeScope_cases hdecl with ⟨j, hk, hdeclOld⟩
  subst hk
  exact openScope_preserves_shifted_ref_realizers hσ hopen hdeclOld


/- =========================================================
   3. 構造 field の preservation
   ========================================================= -/

axiom openScope_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    frameDepthAgreement (pushTypeScope Γ) σ'

axiom openScope_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    shadowingCompatible (pushTypeScope Γ) σ'

axiom openScope_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ x τ, runtimeFrameBindsObject σ' k x τ a

axiom openScope_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    refBindingsNeverOwned σ'

axiom openScope_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    allObjectBindingsOwned σ'

axiom openScope_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ownedAddressesNoDupPerFrame σ'

axiom openScope_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ownedAddressesDisjointAcrossFrames σ'

axiom openScope_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    allOwnedAddressesNamed σ'

axiom openScope_preserves_initializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsObject σ' k x τ a →
      heapInitializedTypedAt σ' a τ ∨ True

theorem openScope_preserves_heapStoredValuesTyped
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ hopen
  rcases hopen with rfl
  intro a c v hheap hval
  simpa using hσ.heapStoredValuesTyped a c v hheap hval

axiom openScope_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    nextFreshAgainstOwned σ'

axiom openScope_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ a j},
      runtimeFrameBindsRef σ' k x τ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a


/- =========================================================
   4. assembled theorem
   ========================================================= -/

theorem openScope_concrete_state_of_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ScopedTypedStateConcrete (pushTypeScope Γ) σ' := by
  intro hσ hopen
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
      heapStoredValuesTyped := ?_
      initializedValuesTyped := ?_
      nextFresh := ?_
      refTargetsAvoidInnerOwned := ?_ }

  · exact openScope_preserves_frameDepthAgreement hσ hopen
  · exact openScope_preserves_shadowingCompatible hσ hopen
  · intro k x τ hdecl
    exact openScope_objectDeclRealized_of_decomposition hσ hopen hdecl
  · intro k x τ hdecl
    exact openScope_refDeclRealized_of_decomposition hσ hopen hdecl
  · intro k a hown
    exact openScope_preserves_ownedAddressNamed hσ hopen hown
  · exact openScope_preserves_refBindingsNeverOwned hσ hopen
  · exact openScope_preserves_allObjectBindingsOwned hσ hopen
  · exact openScope_preserves_ownedNoDupPerFrame hσ hopen
  · exact openScope_preserves_ownedDisjointAcrossFrames hσ hopen
  · exact openScope_preserves_allOwnedAddressesNamed hσ hopen
  · exact openScope_preserves_heapStoredValuesTyped hσ hopen
  · intro k x τ a hbind
    exact openScope_preserves_initializedValuesTyped hσ hopen hbind
  · exact openScope_preserves_nextFreshAgainstOwned hσ hopen
  · intro k x τ a j hbind hjk
    exact openScope_preserves_refTargetsAvoidInnerOwned hσ hopen hbind hjk

theorem openScope_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ScopedTypedStateConcrete (pushTypeScope Γ) σ' := by
  intro hσ hopen
  exact openScope_concrete_state_of_decomposition hσ hopen

end Cpp
