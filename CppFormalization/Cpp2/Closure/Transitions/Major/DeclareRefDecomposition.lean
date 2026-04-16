import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
`DeclareRef` は object を増やさず alias binding だけを top frame に追加する。
したがって preservation は

- type-side では `declareTypeRef` の top 追加の分解
- runtime-side では heap / locals / next が不変であること
- top binding の追加により新 top ref が実現されること

に分かれる。

initializedValuesTyped 系は legacy placeholder (`∨ True`) なので保留する。
また、old object/ref realizer の完全 preservation と
shadowing / ownership の一部は、top-frame transport の細部がまだ重いので
今回は残す。
-/

/-! =========================================================
    1. 環境側の分解
    ========================================================= -/

theorem typeFrameDeclObject_declareTypeRef_inv
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclObject (declareTypeRef Γ x τ) k y υ →
    typeFrameDeclObject Γ k y υ := by
  intro hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      cases k <;>
        simp [declareTypeRef, insertTopDecl, hsc] at hk hdecl
      subst hk
      simp at hdecl
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [declareTypeRef, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy; simp at hdecl
          · refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclObject, declareTypeRef, insertTopDecl, hsc] using hk
          · simpa [declareTypeRef, insertTopDecl, hsc] using hdecl

theorem typeFrameDeclRef_declareTypeRef_cases
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclRef (declareTypeRef Γ x τ) k y υ →
    (k = 0 ∧ y = x ∧ υ = τ) ∨ typeFrameDeclRef Γ k y υ := by
  intro hfresh hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      cases k with
      | zero =>
          -- 先に hk を展開して fr を消去する
          simp [declareTypeRef, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            left
            -- (0, x, τ) のケースであることを示す
            -- hdecl は (fr0.decls.update x (ref τ)) x = some (ref υ) となっている
            simp at hdecl
            exact ⟨rfl, rfl, hdecl.symm⟩
          · right
            -- 既存のフレームにあるケース
            refine ⟨fr0, by simp [hsc], ?_⟩
            -- y ≠ x なので update の影響を受けない
            simpa [hy] using hdecl
      | succ j =>
          right
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclRef, declareTypeRef, insertTopDecl, hsc] using hk
          · simpa [declareTypeRef, insertTopDecl, hsc] using hdecl

/-! =========================================================
    2. 実現子の分解
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

theorem declareRef_realizes_new_top_ref
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    runtimeFrameBindsRef σ' 0 x τ a ∧
    heapLiveTypedAt σ' a τ := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      constructor
      · refine ⟨{ fr with binds := fun y => if y = x then some (.ref τ a) else fr.binds y }, ?_, ?_⟩
        · simp [declareRefState, bindTopBinding, hsc]
        · simp
      · refine ⟨c, ?_, hty, halive⟩
        simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hheap

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
    ========================================================= -/

theorem declareRef_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    frameDepthAgreement (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hΓ : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hΓ] at hfresh
  | cons Γfr Γrs =>
      cases hσs : σ.scopes with
      | nil =>
          simp [currentScopeFresh, hσs] at hsfresh
      | cons σfr σrs =>
          simpa [frameDepthAgreement, declareTypeRef, insertTopDecl, hΓ,
            declareRefState, bindTopBinding, hσs] using hσ.frameDepth

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

theorem declareRef_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ownedAddressesNoDupPerFrame σ' := by
  intro hσ hdecl k fr hk
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  -- σ.scopes の状態で場合分け
  cases hsc : σ.scopes with
  | nil =>
      -- σ.scopes が空のとき、hsfresh から矛盾を導くか、k=0 のケースを直接解く
      simp [declareRefState, bindTopBinding, hsc] at hk
      cases k with
      | zero =>
          -- 新しく作られた 0番目のフレームの locals は [] なので Nodup
          simp at hk
          subst hk
          simp -- [] の Nodup は自明
      | succ j =>
          -- 0番目しかないので succ は存在しない
          simp at hk
  | cons fr0 frs =>
      -- σ.scopes が fr0 :: frs のとき
      simp [declareRefState, bindTopBinding, hsc] at hk
      cases k with
      | zero =>
          -- 0番目のフレームの locals は fr0.locals と同じ
          simp at hk
          subst hk
          -- hσ.ownedNoDupPerFrame の 0 番目の知識を使う
          exact hσ.ownedNoDupPerFrame 0 fr0 (by simp [hsc])
      | succ j =>
          -- 1番目以降のフレームも元の σ と同じ
          exact hσ.ownedNoDupPerFrame (j + 1) fr (by simpa [hsc] using hk)

theorem declareRef_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ownedAddressesDisjointAcrossFrames σ' := by
  intro hσ hdecl i j fi fj addr hij hi hj
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  -- 1. σ.scopes の構造で場合分けして match を解消
  cases hsc : σ.scopes with
  | nil =>
      -- σ.scopes が空のとき、新しい scopes は [new_fr] のみ
      simp [declareRefState, bindTopBinding, hsc] at hi hj
      -- i, j ともに 0 になるはずだが、hij : i ≠ j なので矛盾
      cases i <;> cases j <;> simp at hij hi hj
  | cons fr0 frs =>
      -- 2. σ.scopes = fr0 :: frs のとき、新しい scopes = (update fr0) :: frs
      simp [declareRefState, bindTopBinding, hsc] at hi hj
      -- i, j の位置（トップフレームか、それ以外か）で場合分け
      cases i with
      | zero =>
          simp at hi; subst hi -- fi は更新後のトップフレーム
          cases j with
          | zero => simp at hij -- i=0, j=0 は矛盾
          | succ j' =>
              simp at hj -- fj は元のフレーム
              -- fi.locals は fr0.locals と同じであることを利用
              -- hσ.ownedDisjoint 0 (j'+1) ... を使う
              exact hσ.ownedDisjoint 0 (j' + 1) fr0 fj addr (by simp) (by simp [hsc]) (by simp [hsc, hj])
      | succ i' =>
          simp at hi -- fi は元のフレーム
          cases j with
          | zero =>
              simp at hj; subst hj -- fj は更新後のトップフレーム
              -- hσ.ownedDisjoint (i'+1) 0 ... を使う
              exact hσ.ownedDisjoint (i' + 1) 0 fi fr0 addr (by simp) (by simp [hsc, hi]) (by simp [hsc])
          | succ j' =>
              -- 両方とも既存の古いフレーム
              simp at hj
              have hij' : i' ≠ j' := by intro h; subst h; exact hij rfl
              exact hσ.ownedDisjoint (i' + 1) (j' + 1) fi fj addr hij (by simp [hsc, hi]) (by simp [hsc, hj])

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

theorem declareRefState_heap_eq
    (σ : State) (τ : CppType) (x : Ident) (a0 : Nat) :
    (declareRefState σ τ x a0).heap = σ.heap := by
  unfold declareRefState bindTopBinding
  split <;> rfl

theorem declareRef_preserves_heapStoredValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a0 σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ hdecl
  rcases hdecl with ⟨_, c, hheap, hty, halive, rfl⟩
  intro a c' v hheap' hval
  rw [declareRefState_heap_eq] at hheap'
  exact hσ.heapStoredValuesTyped a c' v hheap' hval

theorem declareRef_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    nextFreshAgainstOwned σ' := by
  intro hσ hdecl
  rcases hdecl with ⟨_, _, _, _, _, rfl⟩
  rcases hσ.nextFresh with ⟨hnext_heap, hnext_locals⟩
  constructor
  · -- heap は変わらない
    simpa [declareRefState_heap_eq] using hnext_heap
  · -- locals も変わらない
    intro k fr hk
    -- hk を σ.scopes に関する命題に書き換える
    cases hsc : σ.scopes with
    | nil =>
      simp [declareRefState, bindTopBinding, hsc] at hk
      cases k with
      | zero =>
          -- hk : [new_fr][0]? = some fr  =>  some new_fr = some fr
          simp at hk
          subst hk -- ここで fr が具体的なフレームに置き換わる
          -- fr.locals は [] なので、中身が何であれ ∈ は矛盾
          simp [declareRefState, bindTopBinding, hsc]
      | succ j =>
          -- 要素が1つしかないので、インデックスが 1 以上の場合は none = some fr で矛盾
          simp at hk
    | cons fr0 frs =>
        simp [declareRefState, bindTopBinding, hsc] at hk
        cases k with
        | zero =>
            simp at hk; subst hk
            simp [declareRefState, bindTopBinding, hsc]
          -- これでゴールが ¬σ.next ∈ fr0.locals になるはずです
            exact hnext_locals 0 fr0 (by simp [hsc])
        | succ j =>
          simp at hk
          simp [declareRefState, bindTopBinding, hsc] -- ゴールの next を簡約
          exact hnext_locals (j + 1) fr (by simpa [hsc] using hk)

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
      heapStoredValuesTyped := ?_
      initializedValuesTyped := ?_
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
