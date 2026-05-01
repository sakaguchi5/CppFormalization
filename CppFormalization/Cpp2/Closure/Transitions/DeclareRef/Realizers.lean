import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.RuntimeTransport

namespace Cpp

/-!
# Closure.Transitions.DeclareRef.Realizers

Realizer reconstruction for `DeclareRef`.
-/

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

end Cpp
