import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
# Closure.Transitions.Major.CloseScopeDecomposition

`closeScope` は top frame を落とし、その locals を kill する。
したがって soundness を theorem 化するには、少なくとも

1. post lower binding が pre lower binding から来ること
2. pre lower ownership が post ownership に降りること
3. top-owned 以外の live cell は kill されないこと

が必要になる。

このファイルでは object/ref binding soundness を theorem 化する。
full concrete-state assembly はまだ重いので最後は axiom のまま残す。
-/

/-! =========================================================
    1. close-scope transport axioms
    ========================================================= -/

/-- post の lower object binding は pre の lower object binding に対応する。 -/
axiom closeScope_reflects_lower_object_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsObject σ' k x τ a →
      runtimeFrameBindsObject σ (k + 1) x τ a

/-- post の lower ref binding は pre の lower ref binding に対応する。 -/
axiom closeScope_reflects_lower_ref_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsRef σ' k x τ a →
      runtimeFrameBindsRef σ (k + 1) x τ a

/-- pre の lower ownership は post へ降りる。 -/
axiom closeScope_preserves_lower_ownership
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ (k + 1) a →
      runtimeFrameOwnsAddress σ' k a

/-- lower-owned address は top-owned ではない。 -/
axiom lower_owned_not_top_owned
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    ∀ {k a},
      runtimeFrameOwnsAddress σ (k + 1) a →
      ¬ runtimeFrameOwnsAddress σ 0 a

/-- top-owned 以外の live cell は closeScope 後も live のまま残る。 -/
axiom closeScope_kills_only_top_owned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {a τ},
      ¬ runtimeFrameOwnsAddress σ 0 a →
      heapLiveTypedAt σ a τ →
      heapLiveTypedAt σ' a τ

/-! =========================================================
    2. binding soundness
    ========================================================= -/

theorem closeScope_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    objectBindingSound σ' := by
  intro hσ hclose
  intro k x τ a hbindPost
  have hbindPre :
      runtimeFrameBindsObject σ (k + 1) x τ a :=
    closeScope_reflects_lower_object_bindings hσ hclose hbindPost
  rcases hσ.objectBindingSound hbindPre with ⟨hownPre, hlivePre⟩
  have hownPost :
      runtimeFrameOwnsAddress σ' k a :=
    closeScope_preserves_lower_ownership hσ hclose hownPre
  have hnotTop :
      ¬ runtimeFrameOwnsAddress σ 0 a :=
    lower_owned_not_top_owned hσ hownPre
  have hlivePost :
      heapLiveTypedAt σ' a τ :=
    closeScope_kills_only_top_owned hσ hclose hnotTop hlivePre
  exact ⟨hownPost, hlivePost⟩

theorem closeScope_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    refBindingSound σ' := by
  intro hσ hclose
  intro k x τ a hbindPost
  have hbindPre :
      runtimeFrameBindsRef σ (k + 1) x τ a :=
    closeScope_reflects_lower_ref_bindings hσ hclose hbindPost
  have hlivePre :
      heapLiveTypedAt σ a τ :=
    hσ.refBindingSound hbindPre
  have hnotTop :
      ¬ runtimeFrameOwnsAddress σ 0 a :=
    hσ.refTargetsAvoidInnerOwned hbindPre (Nat.zero_lt_succ k)
  exact closeScope_kills_only_top_owned hσ hclose hnotTop hlivePre

/-! =========================================================
    3. full assembly
    ========================================================= -/

/-
The remaining close-scope fields are still intentionally left as axioms.
The key change in this file is that the new symmetric kernel fields are no longer axiomatic.
-/
axiom closeScope_preserves_concrete_state_via_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedStateConcrete Γ σ'

end Cpp
