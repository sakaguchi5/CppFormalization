import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectRealizers
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectOwnership
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext

namespace Cpp

/-!
# Closure.Transitions.Major.DeclareObjectDecomposition

`declareObject` の final assembly 層。

このファイルでは、
- frame-depth / heap-stored-values / fresh-next といった構造 field
- まだ axiom のまま残す field
- `ScopedTypedStateConcrete` への最終組み立て

だけを扱う。type-side 分解、realizer 回収、ownership transport は
それぞれ専用ファイルへ分離した。
-/

/-! =========================================================
    1. 構造 field の preservation
    ========================================================= -/

theorem declareObject_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    frameDepthAgreement (declareTypeObject Γ x τ) σ' := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hΓ : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hΓ] at hfresh
  | cons Γfr Γrs =>
      cases hσs : σ.scopes with
      | nil =>
          simp [currentScopeFresh, hσs] at hsfresh
      | cons σfr σrs =>
          simpa [frameDepthAgreement, declareTypeObject, insertTopDecl, hΓ,
            declareObjectStateWithNext, setNext, declareObjectStateCore,
            recordLocal, writeHeap, bindTopBinding, hσs] using hσ.frameDepth

axiom declareObject_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    shadowingCompatible (declareTypeObject Γ x τ) σ'

axiom declareObject_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    refBindingsNeverOwned σ'

axiom declareObject_preserves_initializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a},
      runtimeFrameBindsObject σ' k y υ a →
      heapInitializedTypedAt σ' a υ ∨ True

theorem declareObject_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    nextFreshAgainstOwned σ' := by
  intro _ _ hdecl
  rcases hdecl with ⟨aNext, hdeclNext⟩
  rcases declaresObjectWithNext_postCursorFresh hdeclNext with ⟨hheapNone, hlocals⟩
  exact ⟨hheapNone, hlocals⟩

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

/-- オブジェクト宣言はヒープ全体の型整合性を保存する。 -/
theorem declareObject_preserves_heapInitializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ _ hdecl
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobj, hfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hstate⟩
  subst σcore
  subst hstate
  intro a c v hheap hval
  by_cases ha : a = σ.next
  · subst ha
    simp [setNext] at hheap
    subst hheap
    simp at hval
    simp
    rw [hval] at hovcompat
    exact hovcompat
  · have h_other : (setNext (declareObjectStateCore σ τ x ov) aNext).heap a = σ.heap a := by
      simp [setNext]
      cases σ.scopes <;> simp [ha]
    rw [h_other] at hheap
    exact hσ.heapStoredValuesTyped a c v hheap hval

/-! =========================================================
    2. 最終組み立て
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
      heapStoredValuesTyped := ?_
      initializedValuesTyped := ?_
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
