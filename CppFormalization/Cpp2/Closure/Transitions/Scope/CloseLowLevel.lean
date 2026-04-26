import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcretePreservation
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Lemmas.TypeEnv

namespace Cpp

/-!
# Closure.Transitions.Scope.CloseLowLevel

Low-level reflection facts for `CloseScope`.

These are compatibility-level helpers historically exposed from
`Closure.Transitions.OpenCloseLowLevelTheorems`.  The final close-scope
preservation assembly lives in `Scope.ClosePreservation`.
-/

private theorem closeScope_data
    {σ σ' : State} :
    CloseScope σ σ' →
    ∃ fr frs,
      σ.scopes = fr :: frs ∧
      σ' = killLocals { σ with scopes := frs } fr.locals := by
  intro hclose
  rcases popScope?_some_scopes σ σ' hclose with ⟨fr, frs, hsc⟩
  refine ⟨fr, frs, hsc, ?_⟩
  simpa [CloseScope, popScope?, hsc] using hclose.symm

theorem closeScope_reflects_lower_object_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsObject σ' k x τ a →
      runtimeFrameBindsObject σ (k + 1) x τ a := by
  intro _ hclose k x τ a hbind
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hbind with ⟨fr, hk, hb⟩
  refine ⟨fr, ?_, hb⟩
  simpa [hσ', hsc, runtimeFrameBindsObject] using hk

theorem closeScope_reflects_lower_ref_bindings
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsRef σ' k x τ a →
      runtimeFrameBindsRef σ (k + 1) x τ a := by
  intro _ hclose k x τ a hbind
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hbind with ⟨fr, hk, hb⟩
  refine ⟨fr, ?_, hb⟩
  simpa [hσ', hsc, runtimeFrameBindsRef] using hk

theorem closeScope_preserves_lower_ownership
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ (k + 1) a →
      runtimeFrameOwnsAddress σ' k a := by
  intro _ hclose k a hown
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hown with ⟨fr, hk, hm⟩
  refine ⟨fr, ?_, hm⟩
  simpa [hσ', hsc, runtimeFrameOwnsAddress] using hk

theorem lower_owned_not_top_owned
    {Γ : TypeEnv} {σ : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    ∀ {k a},
      runtimeFrameOwnsAddress σ (k + 1) a →
      ¬ runtimeFrameOwnsAddress σ 0 a := by
  intro hσ k a hlower htop
  rcases hlower with ⟨fk, hk, hmemk⟩
  rcases htop with ⟨f0, h0, hmem0⟩
  exact (hσ.ownedDisjoint (k + 1) 0 fk f0 a (by simp) hk h0 hmemk) hmem0

theorem closeScope_kills_only_top_owned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {a τ},
      ¬ runtimeFrameOwnsAddress σ 0 a →
      heapLiveTypedAt σ a τ →
      heapLiveTypedAt σ' a τ := by
  intro _ hclose a τ hnotTop hlive
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hlive with ⟨c, hheap, hty, halive⟩
  have hnotmem : a ∉ fr0.locals := by
    intro hm
    exact hnotTop ⟨fr0, by simp [hsc], hm⟩
  refine ⟨c, ?_, hty, halive⟩
  calc
    σ'.heap a = (killLocals { σ with scopes := frs } fr0.locals).heap a := by simp [hσ']
    _ = ({ σ with scopes := frs }).heap a := by
      simp [heap_killLocals_other, hnotmem]
    _ = σ.heap a := by rfl
    _ = some c := hheap

end Cpp
