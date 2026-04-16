import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness

namespace Cpp

theorem assigns_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ → HasPlaceType Γ p τ → PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ → Assigns σ p v σ' → objectBindingSound σ' := by
  intro hσ _ _ _ hassign k x υ a hbind
  rcases hassign with ⟨a0, c0, _, hheap0, halive0, _, rfl⟩
  have hbind_old : runtimeFrameBindsObject σ k x υ a := by
    simpa [runtimeFrameBindsObject, writeHeap] using hbind
  rcases hσ.objectBindingSound hbind_old with ⟨hown, hlive⟩
  refine ⟨by simpa [runtimeFrameOwnsAddress, writeHeap] using hown, ?_⟩
  rcases hlive with ⟨c, hheap, hty, halive⟩
  by_cases ha : a = a0
  · subst ha
    -- ここで ∃ c の c として、新しく書き込んだ Cell 自体を与えます
    let c_new : Cell := { ty := c0.ty, value := some v, alive := c0.alive }
    refine ⟨c_new, ?_, ?_, halive0⟩
    · -- σ.heap a = some c_new の証明
      simp [writeHeap, c_new]
    · -- c_new.ty = υ の証明
      -- hheap0: σ.heap a = some c0 と hheap: σ.heap a = some c から c0 = c を導く
      simp [hheap0] at hheap
      rw [← hty, ← hheap]
  · -- case neg (a ≠ a0) は今のままで完璧です
    exact ⟨c, by simp [writeHeap, ha, hheap], hty, halive⟩

theorem assigns_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ → HasPlaceType Γ p τ → PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ → Assigns σ p v σ' → refBindingSound σ' := by
  intro hσ _ _ _ hassign k x υ a hbind
  rcases hassign with ⟨a0, c0, _, hheap0, halive0, _, rfl⟩
  have hbind_old : runtimeFrameBindsRef σ k x υ a := by
    simpa [runtimeFrameBindsRef, writeHeap] using hbind
  rcases hσ.refBindingSound hbind_old with ⟨c, hheap, hty, halive⟩
  by_cases ha : a = a0
  · -- case pos (a = a0)
    subst ha
    let c_new : Cell := { ty := c0.ty, value := some v, alive := c0.alive }
    refine ⟨c_new, by simp [writeHeap, c_new], ?_, halive0⟩
    -- ここでは c0 = c を使って hty を繋げる
    simp [hheap0] at hheap
    rw [← hty, ← hheap]
  · -- case neg (a ≠ a0)
    -- ここでは古い c をそのまま使う
    exact ⟨c, by simp [writeHeap, ha, hheap], hty, halive⟩

axiom assigns_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State} {p : PlaceExpr} {τ : CppType} {v : Value} :
    ScopedTypedStateConcrete Γ σ → HasPlaceType Γ p τ → PlaceReadyConcrete Γ σ p τ →
    ValueCompat v τ → Assigns σ p v σ' → ScopedTypedStateConcrete Γ σ'
end Cpp
