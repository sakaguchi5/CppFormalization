import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteOwnershipTransport

namespace Cpp

/-!
`DeclareRef` は object を増やさず alias binding だけを top frame に追加する。
したがって preservation は

- type-side では `declareTypeRef` の top 追加の分解
- runtime-side では heap / locals / next が不変であること
- top binding の追加により新 top ref が実現されること

に分かれる。

今回の段階では、
- old object/ref realizer
- shadowingCompatible
- allObjectBindingsOwned
- refTargetsAvoidInnerOwned

を theorem 化した。

remaining wall:
- `ownedAddressNamed`
- `allOwnedAddressesNamed`
- `refBindingsNeverOwned`

は `declareRefState` 下の forward transport に
`topFrameBindingFresh σ x` を要する。
現状の `ScopedTypedStateConcrete` だけではそれを導けないので、
ここは strengthening をどう本線へ繋ぐかが次の論点になる。
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
          · subst hy
            simp at hdecl
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
          simp [declareTypeRef, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            left
            simp at hdecl
            exact ⟨rfl, rfl, hdecl.symm⟩
          · right
            refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          right
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclRef, declareTypeRef, insertTopDecl, hsc] using hk
          · simpa [declareTypeRef, insertTopDecl, hsc] using hdecl

private theorem typeFrameDeclObject_declareTypeRef_keep
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclObject (declareTypeRef Γ x τ) k y υ →
    k ≠ 0 ∨ y ≠ x := by
  intro hty
  cases k with
  | zero =>
      right
      rcases hty with ⟨fr, hk, hdecl⟩
      intro hy
      subst hy
      cases hsc : Γ.scopes <;> {
        simp [declareTypeRef, insertTopDecl, hsc] at hk hdecl
        simp [← hk] at hdecl
      }
  | succ j =>
      left
      simp

private theorem typeFrameDeclRef_keep_of_fresh
    {Γ : TypeEnv} {x : Ident}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclRef Γ k y υ →
    k ≠ 0 ∨ y ≠ x := by
  intro hfresh hty
  cases k with
  | zero =>
      right
      intro hy
      subst hy
      rcases hty with ⟨fr, hk, hdecl⟩
      cases hsc : Γ.scopes with
      | nil =>
          simp [currentTypeScopeFresh, hsc] at hfresh
      | cons fr0 frs =>
          simp [currentTypeScopeFresh, hsc] at hfresh
          simp [hsc] at hk
          subst hk
          rw [hfresh] at hdecl
          simp at hdecl
  | succ j =>
      left
      simp

private theorem lookupDecl_declareTypeRef_self
    (Γ : TypeEnv) (x : Ident) (τ : CppType) :
    lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by
  unfold lookupDecl
  cases hsc : Γ.scopes <;>
    simp [lookupDeclFrames, declareTypeRef, insertTopDecl, hsc]

private theorem lookupDecl_declareTypeRef_other
    (Γ : TypeEnv) (x y : Ident) (τ : CppType)
    (hy : y ≠ x) :
    lookupDecl (declareTypeRef Γ x τ) y = lookupDecl Γ y := by
  unfold lookupDecl
  cases hsc : Γ.scopes <;>
    simp [lookupDeclFrames, declareTypeRef, insertTopDecl, hsc, hy]

/-! =========================================================
    2. runtime transport
    ========================================================= -/

theorem declareRefState_heap_eq
    (σ : State) (τ : CppType) (x : Ident) (a0 : Nat) :
    (declareRefState σ τ x a0).heap = σ.heap := by
  unfold declareRefState bindTopBinding
  split <;> rfl

private theorem heapLiveTypedAt_declareRefState_forward
    {σ : State} {τ : CppType} {x : Ident} {a0 b : Nat} {υ : CppType} :
    heapLiveTypedAt σ b υ →
    heapLiveTypedAt (declareRefState σ τ x a0) b υ := by
  intro hlive
  rcases hlive with ⟨c, hheap, hty, halive⟩
  refine ⟨c, ?_, hty, halive⟩
  simpa [declareRefState_heap_eq (σ := σ) (τ := τ) (x := x) (a0 := a0)] using hheap

private theorem runtimeFrameBindsObject_declareRefState_forward_of_keep
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {b : Nat} :
    runtimeFrameBindsObject σ k y υ b →
    (k ≠ 0 ∨ y ≠ x) →
    runtimeFrameBindsObject (declareRefState σ τ x a) k y υ b := by
  intro hbind hkeep
  rcases hbind with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [hsc] at hk
      | succ j =>
          simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          have hfr : fr = fr0 := by
            simpa [hsc] using hk.symm
          subst fr
          rcases hkeep with hk_ne | hy
          · contradiction
          · refine ⟨{ fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z }, ?_, ?_⟩
            · simp [declareRefState, bindTopBinding, hsc]
            · simpa [hy] using hb
      | succ j =>
          refine ⟨fr, ?_, ?_⟩
          · simpa [runtimeFrameBindsObject, declareRefState, bindTopBinding, hsc] using hk
          · simpa [runtimeFrameBindsObject, declareRefState, bindTopBinding, hsc] using hb

private theorem runtimeFrameBindsRef_declareRefState_forward_of_keep
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {k : Nat} {y : Ident} {υ : CppType} {b : Nat} :
    runtimeFrameBindsRef σ k y υ b →
    (k ≠ 0 ∨ y ≠ x) →
    runtimeFrameBindsRef (declareRefState σ τ x a) k y υ b := by
  intro hbind hkeep
  rcases hbind with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero =>
          simp [hsc] at hk
      | succ j =>
          simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          have hfr : fr = fr0 := by
            simpa [hsc] using hk.symm
          subst fr
          rcases hkeep with hk_ne | hy
          · contradiction
          · refine ⟨{ fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z }, ?_, ?_⟩
            · simp [declareRefState, bindTopBinding, hsc]
            · simpa [hy] using hb
      | succ j =>
          refine ⟨fr, ?_, ?_⟩
          · simpa [runtimeFrameBindsRef, declareRefState, bindTopBinding, hsc] using hk
          · simpa [runtimeFrameBindsRef, declareRefState, bindTopBinding, hsc] using hb

/-! =========================================================
    3. 実現子の分解
    ========================================================= -/

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
  rcases hσ.objectDeclRealized (typeFrameDeclObject_declareTypeRef_inv hty) with
    ⟨b, hbindOld, hownOld, hliveOld⟩
  rcases hdecl with ⟨_, _, _, _, _, rfl⟩
  have hkeep : k ≠ 0 ∨ y ≠ x :=
    typeFrameDeclObject_declareTypeRef_keep hty
  refine ⟨b, ?_, ?_, ?_⟩
  · exact runtimeFrameBindsObject_declareRefState_forward_of_keep
      (σ := σ) (τ := τ) (x := x) (a := a)
      (k := k) (y := y) (υ := υ) (b := b)
      hbindOld hkeep
  · exact runtimeFrameOwnsAddress_declareRefState_forward
      (σ := σ) (τ := τ) (x := x) (a := a) (addr := b) (k := k) hownOld
  · exact heapLiveTypedAt_declareRefState_forward
      (σ := σ) (τ := τ) (x := x) (a0 := a) (b := b) (υ := υ) hliveOld

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
    subst hk
    subst hy
    subst hυ
    rcases declareRef_realizes_new_top_ref hσ hfresh hdecl with ⟨hbind, hlive⟩
    exact ⟨a, hbind, hlive⟩
  · rcases hσ.refDeclRealized hold with ⟨b, hbindOld, hliveOld⟩
    rcases hdecl with ⟨_, _, _, _, _, rfl⟩
    have hkeep : k ≠ 0 ∨ y ≠ x :=
      typeFrameDeclRef_keep_of_fresh hfresh hold
    refine ⟨b, ?_, ?_⟩
    · exact runtimeFrameBindsRef_declareRefState_forward_of_keep
        (σ := σ) (τ := τ) (x := x) (a := a)
        (k := k) (y := y) (υ := υ) (b := b)
        hbindOld hkeep
    · exact heapLiveTypedAt_declareRefState_forward
        (σ := σ) (τ := τ) (x := x) (a0 := a) (b := b) (υ := υ) hliveOld

/-! =========================================================
    4. binding-soundness
    ========================================================= -/

theorem declareRef_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    objectBindingSound σ' := by
  intro hσ _ hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  intro k y υ b hbind
  cases hsc : σ.scopes with
  | nil =>
      rcases hbind with ⟨fr, hk, hb⟩
      cases k <;>
        simp [declareRefState, bindTopBinding, hsc] at hk hb
      subst hk
      simp at hb
  | cons fr0 frs =>
      cases k with
      | zero =>
          rcases hbind with ⟨fr, hk, hb⟩
          have hfr : fr =
              { fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z } := by
            simpa [runtimeFrameBindsObject, declareRefState, bindTopBinding, hsc] using hk.symm
          subst hfr
          by_cases hy : y = x
          · subst hy
            simp at hb
          · have hbindOld : runtimeFrameBindsObject σ 0 y υ b := by
              refine ⟨fr0, by simp [hsc], ?_⟩
              simpa [hy] using hb
            rcases hσ.objectBindingSound hbindOld with ⟨hownOld, hliveOld⟩
            refine ⟨?_, ?_⟩
            · simpa [runtimeFrameOwnsAddress, declareRefState, bindTopBinding, hsc] using hownOld
            · simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hliveOld
      | succ j =>
          have hbindOld : runtimeFrameBindsObject σ (j + 1) y υ b := by
            simpa [runtimeFrameBindsObject, declareRefState, bindTopBinding, hsc] using hbind
          rcases hσ.objectBindingSound hbindOld with ⟨hownOld, hliveOld⟩
          refine ⟨?_, ?_⟩
          · simpa [runtimeFrameOwnsAddress, declareRefState, bindTopBinding, hsc] using hownOld
          · simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hliveOld

theorem declareRef_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    refBindingSound σ' := by
  intro hσ _ hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  intro k y υ b hbind
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr0 frs =>
      cases k with
      | zero =>
          rcases hbind with ⟨fr, hk, hb⟩
          have hfr : fr =
              { fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z } := by
            simpa [runtimeFrameBindsRef, declareRefState, bindTopBinding, hsc] using hk.symm
          subst hfr
          by_cases hy : y = x
          · subst hy
            have hs : some (Binding.ref τ a) = some (.ref υ b) := by
              simpa using hb
            injection hs with h_inner
            injection h_inner with hτ_eq hab_eq
            subst hτ_eq
            subst hab_eq
            refine ⟨c, ?_, hty, halive⟩
            simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hheap
          · have hbindOld : runtimeFrameBindsRef σ 0 y υ b := by
              refine ⟨fr0, by simp [hsc], ?_⟩
              simpa [hy] using hb
            simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hσ.refBindingSound hbindOld
      | succ j =>
          have hbindOld : runtimeFrameBindsRef σ (j + 1) y υ b := by
            simpa [runtimeFrameBindsRef, declareRefState, bindTopBinding, hsc] using hbind
          simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hσ.refBindingSound hbindOld

/-! =========================================================
    5. 構造 field の preservation
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

theorem declareRef_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    shadowingCompatible (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl y d hlookup
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      by_cases hy : y = x
      · subst hy
        have hd : d = .ref τ := by
          rw [lookupDecl_declareTypeRef_self] at hlookup
          exact (Option.some.inj hlookup).symm
        subst hd
        refine ⟨.ref τ a, ?_, ?_⟩
        · simp
        · simp [DeclMatchesBinding]
      · have hlookupOld : lookupDecl Γ y = some d := by
          simpa [lookupDecl_declareTypeRef_other (Γ := Γ) (x := x) (y := y) (τ := τ) hy] using hlookup
        rcases hσ.shadowing y d hlookupOld with ⟨b, hb, hmatch⟩
        refine ⟨b, ?_, hmatch⟩
        simpa [declareRefState, hy] using hb

private theorem topFrameBindingFresh_of_currentScopeFresh
    {σ : State} {x : Ident} :
    currentScopeFresh σ x →
    topFrameBindingFresh σ x := by
  intro hfresh fr h0
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      have hEq : fr = fr0 := by
        simpa [hsc] using h0.symm
      subst fr
      simpa [currentScopeFresh, hsc] using hfresh

theorem declareRef_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a0 σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ y υ, runtimeFrameBindsObject σ' k y υ a := by
  intro hσ hdecl
  rcases hdecl with ⟨hsfresh, _c, _hheap, _hty, _halive, rfl⟩
  have htopFresh : topFrameBindingFresh σ x :=
    topFrameBindingFresh_of_currentScopeFresh hsfresh
  exact allOwnedAddressesNamed_declareRefState_of_topFresh
    (σ := σ) (τ := τ) (x := x) (a := a0)
    hσ.ownedNamed htopFresh

theorem declareRef_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    refBindingsNeverOwned σ' := by
  intro hσ hdecl
  rcases hdecl with ⟨hsfresh, _c, _hheap, _hty, _halive, rfl⟩
  have htopFresh : topFrameBindingFresh σ x :=
    topFrameBindingFresh_of_currentScopeFresh hsfresh
  exact refBindingsNeverOwned_declareRefState_of_topFresh
    (σ := σ) (τ := τ) (x := x) (a := a)
    hσ.ownedNamed htopFresh

theorem declareRef_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    allObjectBindingsOwned σ' := by
  intro hσ hdecl
  rcases hdecl with ⟨_, _, _, _, _, rfl⟩
  exact allObjectBindingsOwned_declareRefState
    (σ := σ) (τ := τ) (x := x) (a := a) hσ.objectsOwned

theorem declareRef_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ownedAddressesNoDupPerFrame σ' := by
  intro hσ hdecl k fr hk
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [declareRefState, bindTopBinding, hsc] at hk
      cases k with
      | zero =>
          simp at hk
          subst hk
          simp
      | succ j =>
          simp at hk
  | cons fr0 frs =>
      simp [declareRefState, bindTopBinding, hsc] at hk
      cases k with
      | zero =>
          simp at hk
          subst hk
          exact hσ.ownedNoDupPerFrame 0 fr0 (by simp [hsc])
      | succ j =>
          exact hσ.ownedNoDupPerFrame (j + 1) fr (by simpa [hsc] using hk)

theorem declareRef_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ownedAddressesDisjointAcrossFrames σ' := by
  intro hσ hdecl i j fi fj addr hij hi hj
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [declareRefState, bindTopBinding, hsc] at hi hj
      cases i <;> cases j <;> simp at hij hi hj
  | cons fr0 frs =>
      simp [declareRefState, bindTopBinding, hsc] at hi hj
      cases i with
      | zero =>
          simp at hi
          subst hi
          cases j with
          | zero =>
              simp at hij
          | succ j' =>
              exact hσ.ownedDisjoint 0 (j' + 1) fr0 fj addr (by simp) (by simp [hsc]) (by simpa [hsc] using hj)
      | succ i' =>
          simp at hi
          cases j with
          | zero =>
              simp at hj
              subst hj
              exact hσ.ownedDisjoint (i' + 1) 0 fi fr0 addr (by simp) (by simpa [hsc] using hi) (by simp [hsc])
          | succ j' =>
              exact hσ.ownedDisjoint (i' + 1) (j' + 1) fi fj addr hij
                (by simpa [hsc] using hi) (by simpa [hsc] using hj)

theorem declareRef_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    allOwnedAddressesNamed σ' := by
  intro hσ hdecl k addr h_owns
  exact declareRef_preserves_ownedAddressNamed hσ hdecl h_owns

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
  · simpa [declareRefState_heap_eq] using hnext_heap
  · intro k fr hk
    cases hsc : σ.scopes with
    | nil =>
      simp [declareRefState, bindTopBinding, hsc] at hk
      cases k with
      | zero =>
          simp at hk
          subst fr
          simp [declareRefState, bindTopBinding, hsc]
      | succ j =>
          simp at hk
    | cons fr0 frs =>
        simp [declareRefState, bindTopBinding, hsc] at hk
        cases k with
        | zero =>
            simp at hk
            subst hk
            simp [declareRefState, bindTopBinding, hsc]
            exact hnext_locals 0 fr0 (by simp [hsc])
        | succ j =>
          simp at hk
          simp [declareRefState, bindTopBinding, hsc]
          exact hnext_locals (j + 1) fr (by simpa [hsc] using hk)

theorem declareRef_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a0 σ' →
    ∀ {k y υ a j},
      runtimeFrameBindsRef σ' k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a := by
  intro hσ _ hdecl
  rcases hdecl with ⟨_, _, _, _, _, rfl⟩
  exact refTargetsAvoidInnerOwned_declareRefState
    (σ := σ) (τ := τ) (x := x) (r := a0)
    (havoid := by
      intro k y υ a j href hjk
      exact hσ.refTargetsAvoidInnerOwned href hjk)

private theorem frameDeclBindingExactAt_insertTopRef
    {Γfr : TypeFrame} {σfr : ScopeFrame}
    {x : Ident} {τ : CppType} {a : Nat}
    (hexact : frameDeclBindingExactAt Γfr σfr)
    (hfresh : Γfr.decls x = none) :
    frameDeclBindingExactAt
      { decls := fun y => if y = x then some (.ref τ) else Γfr.decls y }
      { binds := fun y => if y = x then some (.ref τ a) else σfr.binds y
        locals := σfr.locals } := by
  constructor
  · intro y d hdecl
    by_cases hy : y = x
    · subst hy
      simp at hdecl
      subst d
      exact ⟨.ref τ a, by simp, by simp [DeclMatchesBinding]⟩
    · have hdeclOld : Γfr.decls y = some d := by
        simpa [hy] using hdecl
      rcases hexact.1 y d hdeclOld with ⟨b, hb, hmatch⟩
      exact ⟨b, by simpa [hy] using hb, hmatch⟩
  · intro y b hbind
    by_cases hy : y = x
    · subst hy
      simp at hbind
      subst b
      exact ⟨.ref τ, by simp, by simp [DeclMatchesBinding]⟩
    · have hbindOld : σfr.binds y = some b := by
        simpa [hy] using hbind
      rcases hexact.2 y b hbindOld with ⟨d, hd, hmatch⟩
      exact ⟨d, by simpa [hy] using hd, hmatch⟩

private theorem framewiseDeclBindingExact_declareTypeRef_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    framewiseDeclBindingExact (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  intro hσ hfresh
  intro k Γfr σfr hkΓ hkσ
  cases hG : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hG] at hfresh
  | cons Γtop Γrest =>
      cases hS : σ.scopes with
      | nil =>
          have hdepth := hσ.frameDepth
          unfold frameDepthAgreement at hdepth
          simp [hG, hS] at hdepth
      | cons σtop σrest =>
          cases k with
          | zero =>
              have hΓfr :
                  Γfr =
                    { decls := fun y => if y = x then some (.ref τ) else Γtop.decls y } := by
                simpa [declareTypeRef, insertTopDecl, hG] using hkΓ.symm
              have hσfr :
                  σfr =
                    { binds := fun y => if y = x then some (.ref τ a) else σtop.binds y
                      locals := σtop.locals } := by
                simpa [declareRefState, bindTopBinding, hS] using hkσ.symm
              subst hΓfr
              subst hσfr
              have hExact0 : frameDeclBindingExactAt Γtop σtop :=
                hσ.namesExact 0 Γtop σtop (by simp [hG]) (by simp [hS])
              have hTopFresh : Γtop.decls x = none := by
                simpa [currentTypeScopeFresh, hG] using hfresh
              exact frameDeclBindingExactAt_insertTopRef
                (Γfr := Γtop) (σfr := σtop) (x := x) (τ := τ) (a := a) hExact0 hTopFresh
          | succ j =>
              have hkΓ_old : Γ.scopes[j.succ]? = some Γfr := by
                simpa [declareTypeRef, insertTopDecl, hG] using hkΓ
              have hkσ_old : σ.scopes[j.succ]? = some σfr := by
                simpa [declareRefState, bindTopBinding, hS] using hkσ
              exact hσ.namesExact (j + 1) Γfr σfr hkΓ_old hkσ_old

theorem declareRef_preserves_framewiseDeclBindingExact
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    framewiseDeclBindingExact (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨_, _, _, _, _, rfl⟩
  exact framewiseDeclBindingExact_declareTypeRef_declareRefState
    (Γ := Γ) (σ := σ) (x := x) (τ := τ) (a := a) hσ hfresh

/-! =========================================================
    6. 最終組み立て
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
      namesExact := ?_
      shadowing := ?_
      objectDeclRealized := ?_
      refDeclRealized := ?_
      objectBindingSound := ?_
      refBindingSound := ?_
      ownedAddressNamed := ?_
      refsNotOwned := ?_
      objectsOwned := ?_
      ownedNoDupPerFrame := ?_
      ownedDisjoint := ?_
      ownedNamed := ?_
      heapStoredValuesTyped := ?_
      nextFresh := ?_
      refTargetsAvoidInnerOwned := ?_ }

  · exact declareRef_preserves_frameDepthAgreement hσ hfresh hdecl
  · exact declareRef_preserves_framewiseDeclBindingExact hσ hfresh hdecl
  · exact declareRef_preserves_shadowingCompatible hσ hfresh hdecl
  · intro k y υ hty
    exact declareRef_objectDeclRealized_of_decomposition hσ hdecl hty
  · intro k y υ hty
    exact declareRef_refDeclRealized_of_decomposition hfresh hσ hdecl hty
  · exact declareRef_preserves_objectBindingSound hσ hfresh hdecl
  · exact declareRef_preserves_refBindingSound hσ hfresh hdecl
  · intro k a hown
    exact declareRef_preserves_ownedAddressNamed hσ hdecl hown
  · exact declareRef_preserves_refBindingsNeverOwned hσ hdecl
  · exact declareRef_preserves_allObjectBindingsOwned hσ hdecl
  · exact declareRef_preserves_ownedNoDupPerFrame hσ hdecl
  · exact declareRef_preserves_ownedDisjointAcrossFrames hσ hdecl
  · exact declareRef_preserves_allOwnedAddressesNamed hσ hdecl
  · exact declareRef_preserves_heapStoredValuesTyped hσ hdecl
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
