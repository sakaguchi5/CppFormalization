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

initializedValuesTyped 系は legacy placeholder (`∨ True`) なので保留し、
それ以外を theorem-backed にする。
-/

/- =========================================================
   1. 環境側の分解
   ========================================================= -/

theorem typeFrameDeclObject_pushTypeScope_cases
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclObject (pushTypeScope Γ) k x τ →
    ∃ j, k = j + 1 ∧ typeFrameDeclObject Γ j x τ := by
  intro hdecl
  rcases hdecl with ⟨fr, hk, hbind⟩
  cases k with
  | zero =>
      simp [pushTypeScope, emptyTypeFrame] at hk hbind
      subst hk
      simp at hbind
  | succ j =>
      refine ⟨j, rfl, ?_⟩
      refine ⟨fr, ?_, ?_⟩
      · simpa [pushTypeScope] using hk
      · simpa [pushTypeScope] using hbind

theorem typeFrameDeclRef_pushTypeScope_cases
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclRef (pushTypeScope Γ) k x τ →
    ∃ j, k = j + 1 ∧ typeFrameDeclRef Γ j x τ := by
  intro hdecl
  rcases hdecl with ⟨fr, hk, hbind⟩
  cases k with
  | zero =>
      simp [ pushTypeScope, emptyTypeFrame] at hk hbind
      subst hk
      simp at hbind
  | succ j =>
      refine ⟨j, rfl, ?_⟩
      refine ⟨fr, ?_, ?_⟩
      · simpa [pushTypeScope] using hk
      · simpa [pushTypeScope] using hbind

/- =========================================================
   2. realizers の preservation
   ========================================================= -/

theorem openScope_preserves_shifted_object_realizers
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclObject Γ k x τ →
      ∃ a,
        runtimeFrameBindsObject σ' (k + 1) x τ a ∧
        runtimeFrameOwnsAddress σ' (k + 1) a ∧
        heapLiveTypedAt σ' a τ := by
  intro hσ hopen k x τ hdecl
  rcases hopen with rfl
  rcases hσ.objectDeclRealized hdecl with ⟨a, hbind, hown, hlive⟩
  exact ⟨a,
    by simpa [runtimeFrameBindsObject, pushScope] using hbind,
    by simpa [runtimeFrameOwnsAddress, pushScope] using hown,
    by simpa [heapLiveTypedAt, pushScope] using hlive⟩

theorem openScope_preserves_shifted_ref_realizers
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclRef Γ k x τ →
      ∃ a,
        runtimeFrameBindsRef σ' (k + 1) x τ a ∧
        heapLiveTypedAt σ' a τ := by
  intro hσ hopen k x τ hdecl
  rcases hopen with rfl
  rcases hσ.refDeclRealized hdecl with ⟨a, hbind, hlive⟩
  exact ⟨a,
    by simpa [runtimeFrameBindsRef, pushScope] using hbind,
    by simpa [heapLiveTypedAt, pushScope] using hlive⟩

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

theorem openScope_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    frameDepthAgreement (pushTypeScope Γ) σ' := by
  intro hσ hopen
  rcases hopen with rfl
  simpa [frameDepthAgreement, pushTypeScope, pushScope] using hσ.frameDepth

theorem openScope_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    shadowingCompatible (pushTypeScope Γ) σ' := by
  intro hσ hopen
  rcases hopen with rfl
  simpa [shadowingCompatible, lookupDecl, lookupDeclFrames,
    lookupBinding, lookupBindingFrames, pushTypeScope, pushScope,
    emptyTypeFrame, emptyScopeFrame] using hσ.shadowing

theorem openScope_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ x τ, runtimeFrameBindsObject σ' k x τ a := by
  intro hσ hopen k a hown
  rcases hopen with rfl
  cases k with
  | zero =>
      simp [runtimeFrameOwnsAddress, pushScope, emptyScopeFrame] at hown
  | succ j =>
      simpa [runtimeFrameOwnsAddress, runtimeFrameBindsObject, pushScope]
        using hσ.ownedAddressNamed hown

theorem openScope_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    refBindingsNeverOwned σ' := by
  intro hσ hopen
  rcases hopen with rfl
  intro k fr x τ a hk hbind hlocal
  cases k with
  | zero =>
      -- 1. pushScope の定義を展開して、0番目のフレームが emptyScopeFrame であることを導く
      simp [pushScope] at hk
      -- 2. fr = emptyScopeFrame なので、fr を置換して消去する
      subst hk
      -- 3. emptyScopeFrame.binds x は none なので、hbind : none = some ... となり矛盾
      simp [emptyScopeFrame] at hbind
  | succ j =>
      -- succ j の場合は、pushScope によって 1 つずれた元の σ の scopes[j] を見ている
      simp [pushScope] at hk
      -- hσ.refsNotOwned を使って、元の状態 σ における性質を適用する
      exact hσ.refsNotOwned j fr x τ a hk hbind hlocal

theorem openScope_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    allObjectBindingsOwned σ' := by
  intro hσ hopen
  rcases hopen with rfl
  intro k x τ a hbind
  -- runtimeFrameBindsObject の定義を展開して fr を取り出す
  rcases hbind with ⟨fr, hk, hfr_bind⟩
  cases k with
  | zero =>
      -- 1. pushScope の 0 番目は emptyScopeFrame
      simp [pushScope] at hk
      subst hk
      -- 2. emptyScopeFrame.binds x = some (Binding.object ...) は矛盾
      simp [emptyScopeFrame] at hfr_bind
  | succ j =>
      -- 1. pushScope の succ j 番目は σ.scopes[j] であることを展開
      simp [pushScope] at hk
      -- 2. ゴールの (pushScope σ) の (j + 1) 番目の所有権は、σ の j 番目の所有権と同じ
      -- simpa を使うと、定義を展開しながら hσ.objectsOwned を適用できます
      simpa [runtimeFrameOwnsAddress, pushScope] using hσ.objectsOwned j x τ a ⟨fr, hk, hfr_bind⟩

theorem openScope_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ownedAddressesNoDupPerFrame σ' := by
  intro hσ hopen
  rcases hopen with rfl
  intro k
  cases k with
  | zero =>
      -- 新しいフレームは emptyScopeFrame なので、ownedAddresses は空リスト []
      simp [pushScope, emptyScopeFrame, List.nodup_nil]
  | succ j =>
      -- 既存のフレームの性質をそのまま使う
      simpa [pushScope] using hσ.ownedNoDupPerFrame j

theorem openScope_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ownedAddressesDisjointAcrossFrames σ' := by
  intro hσ hopen
  rcases hopen with rfl
  -- i, j: フレームのインデックス, fi, fj: 各フレームの内容, a: 所有されているアドレス
  intro i j fi fj a hij hi hj hai
  cases i with
  | zero =>
      -- 1. i = 0 のとき、fi は emptyScopeFrame なのでアドレスを所有できない
      simp [pushScope] at hi
      subst hi
      simp [emptyScopeFrame] at hai
  | succ i' =>
      cases j with
      | zero =>
          -- 2. j = 0 のとき、fj は emptyScopeFrame なのでアドレス a を含むはずがない
          simp [pushScope] at hj
          subst hj
          intro h_in  -- ゴールが a ∈ fj.locals → False の形であれば intro
          simp [emptyScopeFrame] at h_in
      | succ j' =>
          -- 3. i = i'+1, j = j'+1 のとき。元の σ における disjointness を使う
          simp [pushScope] at hi hj
          have hij' : i' ≠ j' := by
            intro h_eq
            subst h_eq
            exact hij rfl
          -- 元の不変条件を適用
          exact hσ.ownedDisjoint i' j' fi fj a hij' hi hj hai

theorem openScope_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    allOwnedAddressesNamed σ' := by
  intro hσ hopen
  intro k a hown
  exact openScope_preserves_ownedAddressNamed hσ hopen hown

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

theorem openScope_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    nextFreshAgainstOwned σ' := by
  intro hσ hopen
  rcases hopen with rfl
  -- σ.next に関する2つの性質を取り出す
  -- hheap : σ.heap σ.next = none
  -- hlocals : ∀ k fr, σ.scopes[k]? = some fr → σ.next ∉ fr.locals
  rcases hσ.nextFresh with ⟨hheap, hlocals⟩
  refine ⟨?_, ?_⟩
  · -- 1. ヒープの next が none であることの保存
    -- pushScope はヒープを変更しないので、そのまま simpa で通ります
    simpa [pushScope] using hheap
  · -- 2. すべてのフレームの locals に next が含まれないこと
    intro k fr hk
    cases k with
    | zero =>
        -- 新しい空のフレームには何も含まれていない
        simp [pushScope] at hk
        subst hk
        simp [emptyScopeFrame]
    | succ j =>
        -- 既存のフレームについては、元の hlocals を適用する
        -- simp [pushScope] at hk により、hk が σ.scopes[j]? = some fr になる
        simp [pushScope] at hk
        exact hlocals j fr hk

theorem openScope_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ a j},
      runtimeFrameBindsRef σ' k x τ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a := by
  intro hσ hopen k x τ a j hbind hjk
  rcases hopen with rfl
  cases k with
  | zero =>
      simp [runtimeFrameBindsRef, pushScope, emptyScopeFrame] at hbind
  | succ k' =>
      cases j with
      | zero =>
          intro hown
          simp [runtimeFrameOwnsAddress, pushScope, emptyScopeFrame] at hown
      | succ j' =>
          have hjk' : j' < k' := by
            exact Nat.lt_of_succ_lt_succ hjk
          simpa [runtimeFrameBindsRef, runtimeFrameOwnsAddress, pushScope]
            using hσ.refTargetsAvoidInnerOwned hbind hjk'

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
