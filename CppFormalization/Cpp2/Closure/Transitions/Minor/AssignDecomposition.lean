import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness

namespace Cpp

/-!
`Assigns` は frame 構造や ownership を変えず、
既存の live cell の value だけを書き換える操作として扱う。
したがって preservation の本体は、
- realizers の live/typed が壊れないこと
- ownership / freshness / shadowing が不変であること
の分解になる。

initializedValuesTyped 系は legacy placeholder (`∨ True`) なので保留し、
それ以外を theorem-backed にする。
-/

/- =========================================================
   1. realizers の preservation
   ========================================================= -/

theorem assigns_preserves_object_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ∀ {k x υ},
      typeFrameDeclObject Γ k x υ →
      ∃ a,
        runtimeFrameBindsObject σ' k x υ a ∧
        runtimeFrameOwnsAddress σ' k a ∧
        heapLiveTypedAt σ' a υ := by
  intro hσ _ _ _ hassign k x υ hdecl
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  rcases hσ.objectDeclRealized hdecl with ⟨a, hbind, hown, hlive⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa [runtimeFrameBindsObject, writeHeap] using hbind
  · simpa [runtimeFrameOwnsAddress, writeHeap] using hown
  · rcases hlive with ⟨c, hheap, hty, halive⟩
    by_cases ha : a = a0
    · subst ha
      have hc : c = c0 := Option.some.inj (hheap.symm.trans hheap0)
      subst hc
      refine ⟨{ c with value := some v }, ?_, ?_, ?_⟩
      · simp [writeHeap]
      · simpa using hty
      · simp [halive0]
    · refine ⟨c, ?_, hty, halive⟩
      simp [writeHeap, ha, hheap]

theorem assigns_preserves_ref_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ∀ {k x υ},
      typeFrameDeclRef Γ k x υ →
      ∃ a,
        runtimeFrameBindsRef σ' k x υ a ∧
        heapLiveTypedAt σ' a υ := by
  intro hσ _ _ _ hassign k x υ hdecl
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  rcases hσ.refDeclRealized hdecl with ⟨a, hbind, hlive⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [runtimeFrameBindsRef, writeHeap] using hbind
  · rcases hlive with ⟨c, hheap, hty, halive⟩
    by_cases ha : a = a0
    · subst ha
      have hc : c = c0 := Option.some.inj (hheap.symm.trans hheap0)
      subst hc
      refine ⟨{ c with value := some v }, ?_, ?_, ?_⟩
      · simp [writeHeap]
      · simpa using hty
      · simp [halive0]
    · refine ⟨c, ?_, hty, halive⟩
      simp [writeHeap, ha, hheap]

/- =========================================================
   2. 構造 field の preservation
   ========================================================= -/

theorem assigns_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    frameDepthAgreement Γ σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [frameDepthAgreement, writeHeap] using hσ.frameDepth

theorem assigns_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    shadowingCompatible Γ σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [shadowingCompatible, lookupBinding, writeHeap] using hσ.shadowing

theorem assigns_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ x υ, runtimeFrameBindsObject σ' k x υ a := by
  intro hσ _ _ _ hassign k a hown
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [runtimeFrameOwnsAddress, runtimeFrameBindsObject, writeHeap]
    using hσ.ownedAddressNamed hown

theorem assigns_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    refBindingsNeverOwned σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [refBindingsNeverOwned, writeHeap] using hσ.refsNotOwned

theorem assigns_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    allObjectBindingsOwned σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [allObjectBindingsOwned, runtimeFrameBindsObject, runtimeFrameOwnsAddress, writeHeap]
    using hσ.objectsOwned

theorem assigns_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ownedAddressesNoDupPerFrame σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [ownedAddressesNoDupPerFrame, writeHeap] using hσ.ownedNoDupPerFrame

theorem assigns_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ownedAddressesDisjointAcrossFrames σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [ownedAddressesDisjointAcrossFrames, writeHeap] using hσ.ownedDisjoint

theorem assigns_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    allOwnedAddressesNamed σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [allOwnedAddressesNamed, runtimeFrameOwnsAddress, runtimeFrameBindsObject, writeHeap]
    using hσ.ownedNamed

axiom assigns_preserves_initializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ∀ {k x υ a},
      runtimeFrameBindsObject σ' k x υ a →
      heapInitializedTypedAt σ' a υ ∨ True

theorem assigns_preserves_heapStoredValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  intro a c v' hheap hval
  by_cases ha : a = a0
  · subst a
    rw [heap_writeHeap_self] at hheap
    injection hheap with hc
    subst hc
    have hsome : some v = some v' := by
      simpa using hval
    have hvEq : v = v' := by
      injection hsome with h
    subst hvEq
    simpa using hvcompat0
  · rw [heap_writeHeap_other (σ := σ) (a := a0) (b := a)
        (c := { c0 with value := some v }) ha] at hheap
    exact hσ.heapStoredValuesTyped a c v' hheap hval

theorem assigns_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    nextFreshAgainstOwned σ' := by
  intro hσ _ _ _ hassign
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  rcases hσ.nextFresh with ⟨hnextHeap, hnextLocals⟩
  refine ⟨?_, ?_⟩
  · have hne : σ.next ≠ a0 := by
      intro hEq
      subst hEq
      rw [hnextHeap] at hheap0
      cases hheap0
    simp [writeHeap, hne, hnextHeap]
  · simpa [writeHeap] using hnextLocals

theorem assigns_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ∀ {k x υ a j},
      runtimeFrameBindsRef σ' k x υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a := by
  intro hσ _ _ _ hassign k x υ a j hbind hjk
  rcases hassign with ⟨a0, c0, hplace, hheap0, halive0, hvcompat0, rfl⟩
  simpa [runtimeFrameBindsRef, runtimeFrameOwnsAddress, writeHeap]
    using hσ.refTargetsAvoidInnerOwned hbind hjk

/- =========================================================
   3. assembled theorem
   ========================================================= -/

theorem assigns_concrete_state_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hty hready hvcompat hassign
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

  · exact assigns_preserves_frameDepthAgreement hσ hty hready hvcompat hassign
  · exact assigns_preserves_shadowingCompatible hσ hty hready hvcompat hassign
  · intro k x υ hdecl
    exact assigns_preserves_object_realizers hσ hty hready hvcompat hassign hdecl
  · intro k x υ hdecl
    exact assigns_preserves_ref_realizers hσ hty hready hvcompat hassign hdecl
  · intro k a hown
    exact assigns_preserves_ownedAddressNamed hσ hty hready hvcompat hassign hown
  · exact assigns_preserves_refBindingsNeverOwned hσ hty hready hvcompat hassign
  · exact assigns_preserves_allObjectBindingsOwned hσ hty hready hvcompat hassign
  · exact assigns_preserves_ownedNoDupPerFrame hσ hty hready hvcompat hassign
  · exact assigns_preserves_ownedDisjointAcrossFrames hσ hty hready hvcompat hassign
  · exact assigns_preserves_allOwnedAddressesNamed hσ hty hready hvcompat hassign
  · intro a c v' hheap hval
    exact assigns_preserves_heapStoredValuesTyped hσ hty hready hvcompat hassign a c v' hheap hval
  · intro k x υ a hbind
    exact assigns_preserves_initializedValuesTyped hσ hty hready hvcompat hassign hbind
  · exact assigns_preserves_nextFreshAgainstOwned hσ hty hready hvcompat hassign
  · intro k x υ a j hbind hjk
    exact assigns_preserves_refTargetsAvoidInnerOwned
      hσ hty hready hvcompat hassign hbind hjk

theorem assigns_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hty hready hvcompat hassign
  exact assigns_concrete_state_of_decomposition hσ hty hready hvcompat hassign

end Cpp
