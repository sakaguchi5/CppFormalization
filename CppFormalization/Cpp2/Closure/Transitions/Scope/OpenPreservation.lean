import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcretePreservation
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Lemmas.TypeEnv

namespace Cpp

/-!
# Closure.Transitions.Scope.OpenPreservation

Open-scope transition preservation facts.

Opening a scope pushes an empty type frame and an empty runtime frame.  The
existing declarations and runtime bindings shift by one frame, while the heap,
locals outside the new frame, and the fresh cursor are unchanged.
-/

section PushScopeHelpers

private theorem typeFrameDeclObject_pushTypeScope_zero_false
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    ¬ typeFrameDeclObject (pushTypeScope Γ) 0 x τ := by
  intro h
  rcases h with ⟨fr, hk, hdecl⟩
  simp [pushTypeScope, emptyTypeFrame] at hk
  subst fr
  simp at hdecl

private theorem typeFrameDeclRef_pushTypeScope_zero_false
    {Γ : TypeEnv} {x : Ident} {τ : CppType} :
    ¬ typeFrameDeclRef (pushTypeScope Γ) 0 x τ := by
  intro h
  rcases h with ⟨fr, hk, hdecl⟩
  simp [pushTypeScope, emptyTypeFrame] at hk
  subst fr
  simp at hdecl

private theorem typeFrameDeclObject_pushTypeScope_succ_iff
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclObject (pushTypeScope Γ) k.succ x τ ↔
      typeFrameDeclObject Γ k x τ := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hdecl⟩
    exact ⟨fr, by simpa [typeFrameDeclObject, pushTypeScope] using hk, hdecl⟩
  · rcases h with ⟨fr, hk, hdecl⟩
    exact ⟨fr, by simpa [typeFrameDeclObject, pushTypeScope] using hk, hdecl⟩

private theorem typeFrameDeclRef_pushTypeScope_succ_iff
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclRef (pushTypeScope Γ) k.succ x τ ↔
      typeFrameDeclRef Γ k x τ := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hdecl⟩
    exact ⟨fr, by simpa [typeFrameDeclRef, pushTypeScope] using hk, hdecl⟩
  · rcases h with ⟨fr, hk, hdecl⟩
    exact ⟨fr, by simpa [typeFrameDeclRef, pushTypeScope] using hk, hdecl⟩

private theorem runtimeFrameBindsObject_pushScope_zero_false
    {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    ¬ runtimeFrameBindsObject (pushScope σ) 0 x τ a := by
  intro h
  rcases h with ⟨fr, hk, hb⟩
  simp [ pushScope, emptyScopeFrame] at hk
  subst fr
  simp at hb

private theorem runtimeFrameBindsRef_pushScope_zero_false
    {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    ¬ runtimeFrameBindsRef (pushScope σ) 0 x τ a := by
  intro h
  rcases h with ⟨fr, hk, hb⟩
  simp [pushScope, emptyScopeFrame] at hk
  subst fr
  simp at hb

private theorem runtimeFrameBindsObject_pushScope_succ_iff
    {σ : State} {k : Nat} {x : Ident} {τ : CppType} {a : Nat} :
    runtimeFrameBindsObject (pushScope σ) k.succ x τ a ↔
      runtimeFrameBindsObject σ k x τ a := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsObject, pushScope] using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsObject, pushScope] using hk, hb⟩

private theorem runtimeFrameBindsRef_pushScope_succ_iff
    {σ : State} {k : Nat} {x : Ident} {τ : CppType} {a : Nat} :
    runtimeFrameBindsRef (pushScope σ) k.succ x τ a ↔
      runtimeFrameBindsRef σ k x τ a := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsRef, pushScope] using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa [runtimeFrameBindsRef, pushScope] using hk, hb⟩

private theorem heapLiveTypedAt_pushScope_iff
    {σ : State} {a : Nat} {τ : CppType} :
    heapLiveTypedAt (pushScope σ) a τ ↔ heapLiveTypedAt σ a τ := by
  constructor <;> intro h
  · rcases h with ⟨c, hheap, hty, halive⟩
    exact ⟨c, by simpa [heapLiveTypedAt, pushScope] using hheap, hty, halive⟩
  · rcases h with ⟨c, hheap, hty, halive⟩
    exact ⟨c, by simpa [heapLiveTypedAt, pushScope] using hheap, hty, halive⟩

end PushScopeHelpers

private theorem frameDeclBindingExactAt_pushScope_zero:
    frameDeclBindingExactAt emptyTypeFrame emptyScopeFrame := by
  constructor
  · intro x d hdecl
    simp [emptyTypeFrame] at hdecl
  · intro x b hbind
    simp [emptyScopeFrame] at hbind

private theorem framewiseDeclBindingExact_pushScope
    {Γ : TypeEnv} {σ : State} :
    framewiseDeclBindingExact Γ σ →
    framewiseDeclBindingExact (pushTypeScope Γ) (pushScope σ) := by
  intro hexact k Γfr σfr hΓk hσk
  cases k with
  | zero =>
      simp [pushTypeScope, pushScope] at hΓk hσk
      subst Γfr; subst σfr
      exact frameDeclBindingExactAt_pushScope_zero
  | succ k' =>
      simp [pushTypeScope, pushScope] at hΓk hσk
      exact hexact k' Γfr σfr hΓk hσk

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
      simp at h0
  | succ j =>
      have hbind_old : runtimeFrameBindsRef σ j x τ a := by
        simpa [runtimeFrameBindsRef, pushScope] using hbind
      simpa [heapLiveTypedAt, pushScope] using hσ.refBindingSound hbind_old

theorem openScope_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete Γ σ → OpenScope σ σ' → ScopedTypedStateConcrete (pushTypeScope Γ) σ' := by
  intro hσ hopen
  subst σ'
  refine
    { frameDepth := by
        exact (frameDepthAgreement_pushScope (Γ := Γ) (σ := σ)).2 hσ.frameDepth
      namesExact := by
        exact framewiseDeclBindingExact_pushScope (Γ := Γ) (σ := σ) hσ.namesExact
      shadowing := by
        intro x d hdecl
        have hdeclOld : lookupDecl Γ x = some d := by simpa [lookupDecl_pushTypeScope] using hdecl
        rcases hσ.shadowing x d hdeclOld with ⟨b, hb, hmatch⟩
        exact ⟨b, by simpa [lookupBinding_pushScope] using hb, hmatch⟩
      objectDeclRealized := by
        intro k x τ hdecl
        cases k with
        | zero =>
            exfalso
            exact typeFrameDeclObject_pushTypeScope_zero_false hdecl
        | succ k =>
            have hdeclOld : typeFrameDeclObject Γ k x τ :=
              (typeFrameDeclObject_pushTypeScope_succ_iff (Γ := Γ) (k := k) (x := x) (τ := τ)).1 hdecl
            rcases hσ.objectDeclRealized hdeclOld with ⟨a, hbind, hown, hlive⟩
            exact ⟨a,
              (runtimeFrameBindsObject_pushScope_succ_iff (σ := σ) (k := k) (x := x) (τ := τ) (a := a)).2 hbind,
              (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := k) (a := a)).2 hown,
              (heapLiveTypedAt_pushScope_iff (σ := σ) (a := a) (τ := τ)).2 hlive⟩
      refDeclRealized := by
        intro k x τ hdecl
        cases k with
        | zero =>
            exfalso
            exact typeFrameDeclRef_pushTypeScope_zero_false hdecl
        | succ k =>
            have hdeclOld : typeFrameDeclRef Γ k x τ :=
              (typeFrameDeclRef_pushTypeScope_succ_iff (Γ := Γ) (k := k) (x := x) (τ := τ)).1 hdecl
            rcases hσ.refDeclRealized hdeclOld with ⟨a, hbind, hlive⟩
            exact ⟨a,
              (runtimeFrameBindsRef_pushScope_succ_iff (σ := σ) (k := k) (x := x) (τ := τ) (a := a)).2 hbind,
              (heapLiveTypedAt_pushScope_iff (σ := σ) (a := a) (τ := τ)).2 hlive⟩
      objectBindingSound := by
        intro k x τ a hbind
        cases k with
        | zero => exfalso; exact runtimeFrameBindsObject_pushScope_zero_false hbind
        | succ k =>
            have hbindOld : runtimeFrameBindsObject σ k x τ a :=
              (runtimeFrameBindsObject_pushScope_succ_iff (σ := σ) (k := k) (x := x) (τ := τ) (a := a)).1 hbind
            rcases hσ.objectBindingSound hbindOld with ⟨hown, hlive⟩
            exact ⟨
              (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := k) (a := a)).2 hown,
              (heapLiveTypedAt_pushScope_iff (σ := σ) (a := a) (τ := τ)).2 hlive⟩
      refBindingSound := by
        intro k x τ a hbind
        cases k with
        | zero => exfalso; exact runtimeFrameBindsRef_pushScope_zero_false hbind
        | succ k =>
            have hbindOld : runtimeFrameBindsRef σ k x τ a :=
              (runtimeFrameBindsRef_pushScope_succ_iff (σ := σ) (k := k) (x := x) (τ := τ) (a := a)).1 hbind
            exact (heapLiveTypedAt_pushScope_iff (σ := σ) (a := a) (τ := τ)).2 <| hσ.refBindingSound hbindOld
      ownedAddressNamed := by
        intro k a hown
        cases k with
        | zero =>
            exfalso
            exact runtimeFrameOwnsAddress_pushScope_zero_false hown
        | succ k =>
            have hownOld : runtimeFrameOwnsAddress σ k a :=
              (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := k) (a := a)).1 hown
            rcases hσ.ownedAddressNamed hownOld with ⟨x, τ, hbind⟩
            exact ⟨x, τ,
              (runtimeFrameBindsObject_pushScope_succ_iff (σ := σ) (k := k) (x := x) (τ := τ) (a := a)).2 hbind⟩
      refsNotOwned := by
        intro k fr x τ a hk href hmem
        cases k with
        | zero =>
            simp [pushScope, emptyScopeFrame] at hk
            subst fr
            simp at href
        | succ k =>
            have hkOld : σ.scopes[k]? = some fr := by simpa [pushScope] using hk
            exact hσ.refsNotOwned k fr x τ a hkOld href hmem
      objectsOwned := by
        intro k x τ a hbind
        cases k with
        | zero => exfalso; exact runtimeFrameBindsObject_pushScope_zero_false hbind
        | succ k =>
            exact (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := k) (a := a)).2 <|
              hσ.objectsOwned k x τ a <|
                (runtimeFrameBindsObject_pushScope_succ_iff (σ := σ) (k := k) (x := x) (τ := τ) (a := a)).1 hbind
      ownedNoDupPerFrame := by
        exact (ownedAddressesNoDupPerFrame_pushScope (σ := σ)).2 hσ.ownedNoDupPerFrame
      ownedDisjoint := by
        exact (ownedAddressesDisjointAcrossFrames_pushScope (σ := σ)).2 hσ.ownedDisjoint
      ownedNamed := by
        exact (allOwnedAddressesNamed_pushScope (σ := σ)).2 hσ.ownedNamed
      heapStoredValuesTyped := by
        exact (heapInitializedValuesTyped_pushScope (σ := σ)).2 hσ.heapStoredValuesTyped
      nextFresh := by
        have hfresh : freshAddrAgainstOwned σ σ.next :=
          (freshAddrAgainstOwned_at_next (σ := σ)).2 hσ.nextFresh
        have hfresh' : freshAddrAgainstOwned (pushScope σ) (pushScope σ).next := by
          simpa [next_pushScope] using
            (freshAddrAgainstOwned_pushScope_iff (σ := σ) (a := σ.next)).2 hfresh
        exact (freshAddrAgainstOwned_at_next (σ := pushScope σ)).1 hfresh'
      refTargetsAvoidInnerOwned := by
        intro k x τ a j href hjk hown
        cases k with
        | zero => exact Nat.not_lt_zero _ hjk
        | succ k =>
            have hrefOld : runtimeFrameBindsRef σ k x τ a :=
              (runtimeFrameBindsRef_pushScope_succ_iff (σ := σ) (k := k) (x := x) (τ := τ) (a := a)).1 href
            cases j with
            | zero =>
                exact runtimeFrameOwnsAddress_pushScope_zero_false hown
            | succ j =>
                have hownOld : runtimeFrameOwnsAddress σ j a :=
                  (runtimeFrameOwnsAddress_pushScope_succ_iff (σ := σ) (k := j) (a := a)).1 hown
                exact hσ.refTargetsAvoidInnerOwned hrefOld (Nat.lt_of_succ_lt_succ hjk) hownOld }

end Cpp
