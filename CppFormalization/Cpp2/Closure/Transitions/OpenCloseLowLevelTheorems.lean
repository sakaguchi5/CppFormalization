import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcretePreservation
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Lemmas.TypeEnv

namespace Cpp

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
      -- インデックス 0 の場合: push によって入った空フレーム同士
      simp [pushTypeScope, pushScope] at hΓk hσk
      subst Γfr; subst σfr
      exact frameDeclBindingExactAt_pushScope_zero
  | succ k' =>
      -- インデックス k + 1 の場合: 元の Γ.scopes[k'] と σ.scopes[k'] に帰着
      simp [pushTypeScope, pushScope] at hΓk hσk
      exact hexact k' Γfr σfr hΓk hσk

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

section CloseScopeHelpers

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


end CloseScopeHelpers

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
