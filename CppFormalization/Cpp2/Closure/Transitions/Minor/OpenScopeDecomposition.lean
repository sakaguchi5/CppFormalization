import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Transitions.OpenCloseLowLevelTheorems

namespace Cpp

theorem openScope_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ → OpenScope σ σ' → objectBindingSound σ' := by
  intro hσ hopen k x τ a hbind
  rcases hopen with rfl
  cases k with
  | zero =>
      rcases hbind with ⟨fr, hk, h0⟩
      simp [ pushScope, emptyScopeFrame] at hk h0
      subst hk
      -- 3. emptyScopeFrame.binds x は none なので、hbind : none = some ... となり矛盾
      simp at h0
  | succ j =>
      have hbind_old : runtimeFrameBindsObject σ j x τ a := by
        simpa [runtimeFrameBindsObject, pushScope] using hbind
      rcases hσ.objectBindingSound hbind_old with ⟨hown, hlive⟩
      exact ⟨by simpa [runtimeFrameOwnsAddress, pushScope] using hown,
             by simpa [heapLiveTypedAt, pushScope] using hlive⟩

theorem openScope_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ → OpenScope σ σ' → refBindingSound σ' := by
  intro hσ hopen k x τ a hbind
  rcases hopen with rfl
  cases k with
  | zero =>
      rcases hbind with ⟨fr, hk, h0⟩
      simp [ pushScope, emptyScopeFrame] at hk h0
      subst hk
      -- 3. emptyScopeFrame.binds x は常に none なので、h0 と矛盾する
      simp at h0
  | succ j =>
      have hbind_old : runtimeFrameBindsRef σ j x τ a := by
        simpa [runtimeFrameBindsRef, pushScope] using hbind
      simpa [heapLiveTypedAt, pushScope] using hσ.refBindingSound hbind_old

end Cpp
