import CppFormalization.Cpp2.Closure.Transitions.Minor.StateUpdateRoadmap

namespace Cpp

/-!
# Closure.Transitions.Major.CloseScopeDecomposition

`closeScope` を一発で証明しようとすると失敗しやすい。
このファイルでは、ownership discipline に基づく分解補題の形を固定する。

狙い:
- `declareObject` / `declareRef` / `openScope` / `closeScope` の各操作が
  どの layer の情報を保つかを明示する。
- 特に `closeScope` は「top frame の owned object だけを kill する」ことと
  「外側 frame の binding / live witness を壊さない」ことに分ける。
-/

/-- top frame より下の object binding lookup は `declareObject` で壊れない。 -/
axiom declareObject_preserves_lower_object_bindings
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a},
      runtimeFrameBindsObject σ k y υ a →
      runtimeFrameBindsObject σ' (k+1) y υ a

/-- top frame より下の ref binding lookup は `declareObject` で壊れない。 -/
axiom declareObject_preserves_lower_ref_bindings
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a},
      runtimeFrameBindsRef σ k y υ a →
      runtimeFrameBindsRef σ' (k+1) y υ a

/-- `declareRef` は下位 frame の object binding を変えない。 -/
axiom declareRef_preserves_lower_object_bindings
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    ∀ {k y υ b},
      runtimeFrameBindsObject σ k y υ b →
      runtimeFrameBindsObject σ' (k+1) y υ b

/-- `declareRef` は下位 frame の ref binding も変えない。 -/
axiom declareRef_preserves_lower_ref_bindings
    {Γ : TypeEnv} {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    ∀ {k y υ b},
      runtimeFrameBindsRef σ k y υ b →
      runtimeFrameBindsRef σ' (k+1) y υ b

/-- `openScope` は既存 frame を 1 段下へシフトするだけで壊さない。 -/
axiom openScope_shifts_object_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsObject σ k x τ a →
      runtimeFrameBindsObject σ' (k+1) x τ a

axiom openScope_shifts_ref_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsRef σ k x τ a →
      runtimeFrameBindsRef σ' (k+1) x τ a

axiom openScope_shifts_ownership
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ →
    OpenScope σ σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ k a →
      runtimeFrameOwnsAddress σ' (k+1) a

/-- `closeScope` で kill されるのは top frame の owned object だけ。 -/
axiom closeScope_kills_only_top_owned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {a},
      (¬ runtimeFrameOwnsAddress σ 0 a) →
      ∀ {τ}, heapLiveTypedAt σ a τ → heapLiveTypedAt σ' a τ

/-- `closeScope` で lower frame の object binding 自体は保たれる。 -/
axiom closeScope_preserves_lower_object_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsObject σ (k+1) x τ a →
      runtimeFrameBindsObject σ' k x τ a

/-- `closeScope` で lower frame の ref binding も保たれる。 -/
axiom closeScope_preserves_lower_ref_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsRef σ (k+1) x τ a →
      runtimeFrameBindsRef σ' k x τ a

/-- lower frame が所有していた object は `closeScope` 後も top-kill の対象ではない。 -/
axiom lower_owned_not_top_owned
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    ∀ {k a},
      runtimeFrameOwnsAddress σ (k+1) a →
      ¬ runtimeFrameOwnsAddress σ 0 a

axiom typeFrameDeclObject_pushTypeScope_succ
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclObject Γ k x τ →
    typeFrameDeclObject (pushTypeScope Γ) (k + 1) x τ

theorem closeScope_preserves_outer_runtimeFrameBindsObject
    {Γ : TypeEnv} {σ σ' : State} {k : Nat} {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    runtimeFrameBindsObject σ (k + 1) x τ a →
    runtimeFrameBindsObject σ' k x τ a := by
  intro hσ hclose hbind
  exact closeScope_preserves_lower_object_bindings
    (Γ := Γ) (σ := σ) (σ' := σ') hσ hclose hbind

theorem closeScope_preserves_outer_live_typed
    {Γ : TypeEnv} {σ σ' : State} {k : Nat} {a : Nat} {τ : CppType} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    runtimeFrameOwnsAddress σ (k + 1) a →
    heapLiveTypedAt σ a τ →
    heapLiveTypedAt σ' a τ := by
  intro hσ hclose hown hlive
  have hnotTop : ¬ runtimeFrameOwnsAddress σ 0 a :=
    lower_owned_not_top_owned (Γ := Γ) (σ := σ) hσ hown
  exact closeScope_kills_only_top_owned
    (Γ := Γ) (σ := σ) (σ' := σ') hσ hclose hnotTop hlive

/-- `closeScope` の核心を 2 段で組み立てた theorem 版。 -/
theorem closeScope_preserves_outer_object_realizers
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclObject Γ k x τ →
      ∃ a, runtimeFrameBindsObject σ' k x τ a ∧ heapLiveTypedAt σ' a τ := by
  intro hσ hclose k x τ hdecl
  have hdecl' : typeFrameDeclObject (pushTypeScope Γ) (k + 1) x τ :=
  typeFrameDeclObject_pushTypeScope_succ hdecl
  rcases hσ.objectDeclRealized hdecl' with ⟨a, hbind, hown, hlive⟩
  have hbind' : runtimeFrameBindsObject σ' k x τ a :=
    closeScope_preserves_outer_runtimeFrameBindsObject hσ hclose hbind
  have hlive' : heapLiveTypedAt σ' a τ :=
    closeScope_preserves_outer_live_typed hσ hclose hown hlive
  exact ⟨a, hbind', hlive'⟩

axiom typeFrameDeclRef_pushTypeScope_succ
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclRef Γ k x τ →
    typeFrameDeclRef (pushTypeScope Γ) (k + 1) x τ

/-- `closeScope` 後の ref 実現も lower binding 保存から得る。 -/
theorem closeScope_preserves_outer_ref_realizers
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ},
      typeFrameDeclRef Γ k x τ →
      ∃ a,
        runtimeFrameBindsRef σ' k x τ a ∧
        heapLiveTypedAt σ' a τ := by
  intro hσ hclose k x τ hdecl
  have hdecl' : typeFrameDeclRef (pushTypeScope Γ) (k + 1) x τ :=
    typeFrameDeclRef_pushTypeScope_succ hdecl
  rcases hσ.refDeclRealized hdecl' with ⟨a, hbind, hlive⟩
  have hbind' : runtimeFrameBindsRef σ' k x τ a :=
    closeScope_preserves_lower_ref_bindings hσ hclose hbind
  have hnotTop : ¬ runtimeFrameOwnsAddress σ 0 a :=
    hσ.refTargetsAvoidInnerOwned hbind (by omega)
  have hlive' : heapLiveTypedAt σ' a τ :=
    closeScope_kills_only_top_owned hσ hclose hnotTop hlive
  exact ⟨a, hbind', hlive'⟩


axiom closeScope_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    frameDepthAgreement Γ σ'

axiom closeScope_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    shadowingCompatible Γ σ'

axiom closeScope_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ x τ, runtimeFrameBindsObject σ' k x τ a

axiom closeScope_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    refBindingsNeverOwned σ'

axiom closeScope_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    allObjectBindingsOwned σ'

axiom closeScope_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ownedAddressesNoDupPerFrame σ'

axiom closeScope_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ownedAddressesDisjointAcrossFrames σ'

axiom closeScope_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    allOwnedAddressesNamed σ'

axiom closeScope_preserves_initializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsObject σ' k x τ a →
      heapInitializedTypedAt σ' a τ ∨ True

axiom closeScope_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    nextFreshAgainstOwned σ'

axiom closeScope_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a j},
      runtimeFrameBindsRef σ' k x τ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a

axiom objectBindingOwned_of_allObjectBindingsOwned
    {σ : State} {k : Nat} {x : Ident} {τ : CppType} {a : Nat} :
    allObjectBindingsOwned σ →
    runtimeFrameBindsObject σ k x τ a →
    runtimeFrameOwnsAddress σ k a

theorem object_realizer_of_binding_live_and_owned
    {σ' : State} {k : Nat} {x : Ident} {τ : CppType} :
    allObjectBindingsOwned σ' →
    (∃ a, runtimeFrameBindsObject σ' k x τ a ∧ heapLiveTypedAt σ' a τ) →
    ∃ a,
      runtimeFrameBindsObject σ' k x τ a ∧
      runtimeFrameOwnsAddress σ' k a ∧
      heapLiveTypedAt σ' a τ := by
  intro hOwned h
  rcases h with ⟨a, hbind, hlive⟩
  have hown : runtimeFrameOwnsAddress σ' k a :=
    objectBindingOwned_of_allObjectBindingsOwned hOwned hbind
  exact ⟨a, hbind, hown, hlive⟩

/-- 以上の分解が揃えば `closeScope_preserves_concrete_state` は theorem に落ちる。 -/
theorem closeScope_concrete_state_of_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    (∀ {k x τ}, typeFrameDeclObject Γ k x τ →
      ∃ a, runtimeFrameBindsObject σ' k x τ a ∧ heapLiveTypedAt σ' a τ) →
    (∀ {k x τ}, typeFrameDeclRef Γ k x τ →
      ∃ a, runtimeFrameBindsRef σ' k x τ a ∧ heapLiveTypedAt σ' a τ) →
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hobj href hσ hclose
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

  · exact closeScope_preserves_frameDepthAgreement hσ hclose
  · exact closeScope_preserves_shadowingCompatible hσ hclose
  · intro k x τ hdecl
    exact object_realizer_of_binding_live_and_owned
      (closeScope_preserves_allObjectBindingsOwned hσ hclose)
      (hobj hdecl)
  · intro k x τ hdecl
    exact href hdecl
  · intro k a hown
    exact closeScope_preserves_ownedAddressNamed hσ hclose hown
  · exact closeScope_preserves_refBindingsNeverOwned hσ hclose
  · exact closeScope_preserves_allObjectBindingsOwned hσ hclose
  · exact closeScope_preserves_ownedNoDupPerFrame hσ hclose
  · exact closeScope_preserves_ownedDisjointAcrossFrames hσ hclose
  · exact closeScope_preserves_allOwnedAddressesNamed hσ hclose
  · intro k x τ a hbind
    exact closeScope_preserves_initializedValuesTyped hσ hclose hbind
  · exact closeScope_preserves_nextFreshAgainstOwned hσ hclose
  · intro k x τ a j hbind hjk
    exact closeScope_preserves_refTargetsAvoidInnerOwned hσ hclose hbind hjk



theorem closeScope_preserves_concrete_state_via_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hclose
  refine closeScope_concrete_state_of_decomposition ?_ ?_ hσ hclose
  · intro k x τ hdecl
    exact closeScope_preserves_outer_object_realizers hσ hclose hdecl
  · intro k x τ hdecl
    exact closeScope_preserves_outer_ref_realizers hσ hclose hdecl

end Cpp
