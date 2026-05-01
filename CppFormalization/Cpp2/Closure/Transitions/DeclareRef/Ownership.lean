import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.RuntimeTransport

namespace Cpp

/-!
# Closure.Transitions.DeclareRef.Ownership

Ownership and reference-target discipline preservation for `DeclareRef`.
-/

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

end Cpp
