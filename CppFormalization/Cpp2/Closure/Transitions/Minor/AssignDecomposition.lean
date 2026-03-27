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
-/

/- =========================================================
   1. realizers の preservation
   ========================================================= -/

axiom assigns_preserves_object_realizers
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
        heapLiveTypedAt σ' a υ

axiom assigns_preserves_ref_realizers
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
        heapLiveTypedAt σ' a υ


/- =========================================================
   2. 構造 field の preservation
   ========================================================= -/

axiom assigns_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    frameDepthAgreement Γ σ'

axiom assigns_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    shadowingCompatible Γ σ'

axiom assigns_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ x υ, runtimeFrameBindsObject σ' k x υ a

axiom assigns_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    refBindingsNeverOwned σ'

axiom assigns_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    allObjectBindingsOwned σ'

axiom assigns_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ownedAddressesNoDupPerFrame σ'

axiom assigns_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    ownedAddressesDisjointAcrossFrames σ'

axiom assigns_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    allOwnedAddressesNamed σ'

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

axiom assigns_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ →
    HasPlaceType Γ p τ →
    PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ →
    Assigns σ p v σ' →
    nextFreshAgainstOwned σ'

axiom assigns_preserves_refTargetsAvoidInnerOwned
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
      ¬ runtimeFrameOwnsAddress σ' j a


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
