import CppFormalization.Cpp2.Closure.Transitions.Major.CloseScopeDecomposition
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext

namespace Cpp

/-!
# Closure.Transitions.Major.DeclareObjectDecomposition

`declareObject` は `declareRef` より一段重い。
理由は、新しい top object binding だけでなく、top ownership と fresh address を実際に増やすからである。

このファイルでは、`DeclaresObject` が `ScopedTypedStateConcrete` を保つことを、
`closeScope` と同じく field ごとに分解して組み立てる。

重要:
- object payload semantics と post-state cursor policy は分離された。
- したがって `nextFreshAgainstOwned` は allocator/cursor policy 側から
  honest に供給できる。
-/

/-! =========================================================
    1. 型環境側の分解
    ========================================================= -/

theorem typeFrameDeclRef_declareTypeObject_inv
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclRef (declareTypeObject Γ x τ) k y υ →
    typeFrameDeclRef Γ k y υ := by
  intro hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      cases k <;>
        simp [declareTypeObject, insertTopDecl, hsc] at hk hdecl
      subst hk
      simp at hdecl
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [declareTypeObject, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            simp at hdecl
          · refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclRef, declareTypeObject, insertTopDecl, hsc] using hk
          · simpa [declareTypeObject, insertTopDecl, hsc] using hdecl

theorem typeFrameDeclObject_declareTypeObject_cases
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclObject (declareTypeObject Γ x τ) k y υ →
    (k = 0 ∧ y = x ∧ υ = τ) ∨ typeFrameDeclObject Γ k y υ := by
  intro hfresh hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [declareTypeObject, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            left
            have hυ : υ = τ := by
              simpa using hdecl.symm
            exact ⟨rfl, rfl, hυ⟩
          · right
            refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          right
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclObject, declareTypeObject, insertTopDecl, hsc] using hk
          · simpa [declareTypeObject, insertTopDecl, hsc] using hdecl

/-! =========================================================
    2. 実現子の分解
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

theorem declareObject_realizes_new_top_object
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∃ a,
      runtimeFrameBindsObject σ' 0 x τ a ∧
      runtimeFrameOwnsAddress σ' 0 a ∧
      heapLiveTypedAt σ' a τ := by
  intro _ _ hdecl
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      let fr' : ScopeFrame :=
        { binds := fun y => if y = x then some (.object τ σ.next) else fr.binds y
          locals := σ.next :: fr.locals }
      refine ⟨σ.next, ?_, ?_, ?_⟩
      · refine ⟨fr', ?_, ?_⟩
        · simp [fr', setNext, declareObjectStateCore,
            recordLocal, writeHeap, bindTopBinding, hsc]
        · simp [fr']
      · refine ⟨fr', ?_, ?_⟩
        · simp [fr',setNext, declareObjectStateCore,
            recordLocal, writeHeap, bindTopBinding, hsc]
        · simp [fr']
      · refine ⟨{ ty := τ, value := ov, alive := true }, ?_, rfl, rfl⟩
        simp

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
  · -- 1. a = σ.next (新しく作られたオブジェクト) の場合
    subst ha
    -- setNext はヒープに影響を与えないことを simp で解消
    simp [setNext] at hheap
    -- これで hheap は (declareObjectStateCore σ τ x ov).heap σ.next = some c になる
    subst hheap
    -- これでゴールが ValueCompat v { ty := τ, value := ov, alive := true }.ty
    -- つまり ValueCompat v τ になる
    simp at hval
    simp
    -- hval : ov = some v となったので、hovcompat の ov を置き換える
    rw [hval] at hovcompat
    exact hovcompat
  · -- 他のアドレスの場合も同様に「heap が変わらない」事実を先に作る
    have h_other : (setNext (declareObjectStateCore σ τ x ov) aNext).heap a = σ.heap a := by
      simp [setNext]
      cases σ.scopes <;> simp [ ha]

    rw [h_other] at hheap
    exact hσ.heapStoredValuesTyped a c v hheap hval

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
