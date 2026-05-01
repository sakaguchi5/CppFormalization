import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.Shape

namespace Cpp

/-!
# Closure.Transitions.DeclareRef.RuntimeTransport

Runtime-state transport facts for `declareRefState`.
`DeclareRef` adds a top-frame ref binding but preserves heap, ownership locals,
and lower-frame bindings.
-/

theorem declareRefState_heap_eq
    (σ : State) (τ : CppType) (x : Ident) (a0 : Nat) :
    (declareRefState σ τ x a0).heap = σ.heap := by
  unfold declareRefState bindTopBinding
  split <;> rfl

theorem heapLiveTypedAt_declareRefState_forward
    {σ : State} {τ : CppType} {x : Ident} {a0 b : Nat} {υ : CppType} :
    heapLiveTypedAt σ b υ →
    heapLiveTypedAt (declareRefState σ τ x a0) b υ := by
  intro hlive
  rcases hlive with ⟨c, hheap, hty, halive⟩
  refine ⟨c, ?_, hty, halive⟩
  simpa [declareRefState_heap_eq (σ := σ) (τ := τ) (x := x) (a0 := a0)] using hheap

theorem runtimeFrameBindsObject_declareRefState_forward_of_keep
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
      | zero => simp [hsc] at hk
      | succ j => simp [hsc] at hk
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

theorem runtimeFrameBindsRef_declareRefState_forward_of_keep
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
      | zero => simp [hsc] at hk
      | succ j => simp [hsc] at hk
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

theorem topFrameBindingFresh_of_currentScopeFresh
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

end Cpp
