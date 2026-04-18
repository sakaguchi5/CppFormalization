import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Transitions.OpenCloseLowLevelTheorems
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteStrengthening

namespace Cpp

/-!
# Closure.Transitions.Major.CloseScopeDecomposition

`closeScope` は top frame を落とし、その locals を kill する。
したがって soundness を theorem 化するには、少なくとも

1. post lower binding が pre lower binding から来ること
2. pre lower ownership が post ownership に降りること
3. top-owned 以外の live cell は kill されないこと

が必要になる。

このファイルでは object/ref binding soundness に加えて、
full concrete-state assembly まで theorem 化する。
-/

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

private theorem typeFrameDeclObject_pushTypeScope_succ
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclObject Γ k x τ →
    typeFrameDeclObject (pushTypeScope Γ) (k + 1) x τ := by
  intro h
  rcases h with ⟨fr, hk, hdecl⟩
  exact ⟨fr, by simpa [typeFrameDeclObject, pushTypeScope] using hk, hdecl⟩

private theorem typeFrameDeclRef_pushTypeScope_succ
    {Γ : TypeEnv} {k : Nat} {x : Ident} {τ : CppType} :
    typeFrameDeclRef Γ k x τ →
    typeFrameDeclRef (pushTypeScope Γ) (k + 1) x τ := by
  intro h
  rcases h with ⟨fr, hk, hdecl⟩
  exact ⟨fr, by simpa [typeFrameDeclRef, pushTypeScope] using hk, hdecl⟩

private theorem closeScope_preserves_lower_object_bindings_forward
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsObject σ (k + 1) x τ a →
      runtimeFrameBindsObject σ' k x τ a := by
  intro _ hclose k x τ a hbind
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hbind with ⟨fr, hk, hb⟩
  refine ⟨fr, ?_, hb⟩
  simpa [hσ', hsc, runtimeFrameBindsObject] using hk

private theorem closeScope_preserves_lower_ref_bindings_forward
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k x τ a},
      runtimeFrameBindsRef σ (k + 1) x τ a →
      runtimeFrameBindsRef σ' k x τ a := by
  intro _ hclose k x τ a hbind
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hbind with ⟨fr, hk, hb⟩
  refine ⟨fr, ?_, hb⟩
  simpa [hσ', hsc, runtimeFrameBindsRef] using hk

private theorem closeScope_reflects_lower_ownership
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      runtimeFrameOwnsAddress σ (k + 1) a := by
  intro _ hclose k a hown
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hown with ⟨fr, hk, hm⟩
  refine ⟨fr, ?_, hm⟩
  simpa [hσ', hsc, runtimeFrameOwnsAddress] using hk

private theorem heapInitializedValuesTyped_killAddr
    {σ : State} {a : Nat} :
    heapInitializedValuesTyped σ →
    heapInitializedValuesTyped (killAddr σ a) := by
  intro hinit
  intro b c v hheap hval
  by_cases hba : b = a
  · subst b
    unfold killAddr at hheap
    cases hσa : σ.heap a with
    | none =>
        simp [hσa] at hheap
    | some c0 =>
        have hc : c = { c0 with alive := false } := by
          apply Option.some.inj
          simpa [hσa] using hheap.symm
        subst c
        have hval0 : c0.value = some v := by
          simpa using hval
        exact hinit a c0 v hσa hval0
  · unfold killAddr at hheap
    cases hσa : σ.heap a with
    | none =>
        simp [hσa] at hheap
        exact hinit b c v hheap hval
    | some c0 =>
        have hheap0 : σ.heap b = some c := by
          simpa [writeHeap, hba, hσa] using hheap
        exact hinit b c v hheap0 hval

private theorem heapInitializedValuesTyped_killLocals
    {σ : State} {ls : List Nat} :
    heapInitializedValuesTyped σ →
    heapInitializedValuesTyped (killLocals σ ls) := by
  intro hinit
  induction ls generalizing σ with
  | nil =>
      simpa [killLocals] using hinit
  | cons a ls ih =>
      simpa [killLocals] using ih (σ := killAddr σ a) (heapInitializedValuesTyped_killAddr (σ := σ) (a := a) hinit)

private theorem closeScope_preserves_framewiseDeclBindingExact
    {Γ : TypeEnv} {σ σ' : State} :
    framewiseDeclBindingExact (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    framewiseDeclBindingExact Γ σ' := by
  intro hexact hclose
  intro k Γfr σfr hkΓ hkσ
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  have hkΓ' : (pushTypeScope Γ).scopes[k + 1]? = some Γfr := by
    simpa [pushTypeScope] using hkΓ
  have hkσ' : σ.scopes[k + 1]? = some σfr := by
    simpa [hσ', hsc] using hkσ
  exact hexact (k + 1) Γfr σfr hkΓ' hkσ'

private theorem shadowingCompatibleFrames_of_lists
    {Γs : List TypeFrame} {σs : List ScopeFrame}
    (hlen : Γs.length = σs.length)
    (hexact : ∀ (k : Nat) (Γfr : TypeFrame) (σfr : ScopeFrame),
      Γs[k]? = some Γfr →
      σs[k]? = some σfr →
      frameDeclBindingExactAt Γfr σfr) :
    ∀ x d,
      lookupDeclFrames Γs x = some d →
      ∃ b, lookupBindingFrames σs x = some b ∧ DeclMatchesBinding d b := by
  induction Γs generalizing σs with
  | nil =>
      cases σs with
      | nil =>
          intro x d hdecl
          simp [lookupDeclFrames] at hdecl
      | cons σfr σfs =>
          simp at hlen
  | cons Γfr Γfs ih =>
      cases σs with
      | nil =>
          simp at hlen
      | cons σfr σfs =>
          intro x d hdecl
          have hExact0 : frameDeclBindingExactAt Γfr σfr :=
            hexact 0 Γfr σfr (by simp) (by simp)
          unfold lookupDeclFrames at hdecl
          cases hΓx : Γfr.decls x with
          | none =>
              have hnoneσ : σfr.binds x = none := by
                cases hσx : σfr.binds x with
                | none => simp
                | some b =>
                    rcases frameDeclBindingExactAt_backward hExact0 hσx with ⟨d', htop, _⟩
                    rw [hΓx] at htop
                    simp at htop
              have htail : lookupDeclFrames Γfs x = some d := by
                simpa [hΓx] using hdecl
              have hlenTail : Γfs.length = σfs.length := by
                simpa using Nat.succ.inj hlen
              have hexactTail : ∀ (k : Nat) (Γfr' : TypeFrame) (σfr' : ScopeFrame),
                  Γfs[k]? = some Γfr' →
                  σfs[k]? = some σfr' →
                  frameDeclBindingExactAt Γfr' σfr' := by
                intro k Γfr' σfr' hkΓ hkσ
                exact hexact (k + 1) Γfr' σfr' (by simpa using hkΓ) (by simpa using hkσ)
              rcases ih hlenTail hexactTail x d htail with ⟨b, hb, hmatch⟩
              exact ⟨b, by simpa [lookupBindingFrames, hnoneσ] using hb, hmatch⟩
          | some d0 =>
              have hd0 : d0 = d := by
                simpa [hΓx] using hdecl
              subst hd0
              rcases frameDeclBindingExactAt_forward hExact0 hΓx with ⟨b, hb, hmatch⟩
              exact ⟨b, by simp [lookupBindingFrames, hb], hmatch⟩

private theorem shadowingCompatible_of_framewiseExact
    {Γ : TypeEnv} {σ : State} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    shadowingCompatible Γ σ := by
  intro hdepth hexact x d hdecl
  have hlen : Γ.scopes.length = σ.scopes.length := hdepth
  simpa [lookupDecl, lookupBinding] using
    shadowingCompatibleFrames_of_lists hlen hexact x d hdecl

private theorem closeScope_preserves_objectDeclRealized
    {Γ : TypeEnv} {σ σ' : State}
    (hσ : ScopedTypedStateConcrete (pushTypeScope Γ) σ)
    (hclose : CloseScope σ σ') :
    ∀ {k x τ},
      typeFrameDeclObject Γ k x τ →
      ∃ a,
        runtimeFrameBindsObject σ' k x τ a ∧
        runtimeFrameOwnsAddress σ' k a ∧
        heapLiveTypedAt σ' a τ := by
  intro k x τ hdecl
  have hdeclPre : typeFrameDeclObject (pushTypeScope Γ) (k + 1) x τ :=
    typeFrameDeclObject_pushTypeScope_succ hdecl
  rcases hσ.objectDeclRealized hdeclPre with ⟨a, hbindPre, hownPre, hlivePre⟩
  have hbindPost : runtimeFrameBindsObject σ' k x τ a :=
    closeScope_preserves_lower_object_bindings_forward hσ hclose hbindPre
  have hownPost : runtimeFrameOwnsAddress σ' k a :=
    closeScope_preserves_lower_ownership hσ hclose hownPre
  have hnotTop : ¬ runtimeFrameOwnsAddress σ 0 a :=
    lower_owned_not_top_owned hσ hownPre
  have hlivePost : heapLiveTypedAt σ' a τ :=
    closeScope_kills_only_top_owned hσ hclose hnotTop hlivePre
  exact ⟨a, hbindPost, hownPost, hlivePost⟩

private theorem closeScope_preserves_refDeclRealized
    {Γ : TypeEnv} {σ σ' : State}
    (hσ : ScopedTypedStateConcrete (pushTypeScope Γ) σ)
    (hclose : CloseScope σ σ') :
    ∀ {k x τ},
      typeFrameDeclRef Γ k x τ →
      ∃ a,
        runtimeFrameBindsRef σ' k x τ a ∧
        heapLiveTypedAt σ' a τ := by
  intro k x τ hdecl
  have hdeclPre : typeFrameDeclRef (pushTypeScope Γ) (k + 1) x τ :=
    typeFrameDeclRef_pushTypeScope_succ hdecl
  rcases hσ.refDeclRealized hdeclPre with ⟨a, hbindPre, hlivePre⟩
  have hbindPost : runtimeFrameBindsRef σ' k x τ a :=
    closeScope_preserves_lower_ref_bindings_forward hσ hclose hbindPre
  have hnotTop : ¬ runtimeFrameOwnsAddress σ 0 a :=
    hσ.refTargetsAvoidInnerOwned hbindPre (Nat.zero_lt_succ k)
  have hlivePost : heapLiveTypedAt σ' a τ :=
    closeScope_kills_only_top_owned hσ hclose hnotTop hlivePre
  exact ⟨a, hbindPost, hlivePost⟩

private theorem closeScope_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State}
    (hσ : ScopedTypedStateConcrete (pushTypeScope Γ) σ)
    (hclose : CloseScope σ σ') :
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ x τ, runtimeFrameBindsObject σ' k x τ a := by
  intro k a hownPost
  have hownPre : runtimeFrameOwnsAddress σ (k + 1) a :=
    closeScope_reflects_lower_ownership hσ hclose hownPost
  rcases hσ.ownedAddressNamed hownPre with ⟨x, τ, hbindPre⟩
  exact ⟨x, τ, closeScope_preserves_lower_object_bindings_forward hσ hclose hbindPre⟩

private theorem closeScope_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ownedAddressesNoDupPerFrame σ' := by
  intro hσ hclose k fr hk
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  have hkPre : σ.scopes[k + 1]? = some fr := by
    simpa [hσ', hsc] using hk
  exact hσ.ownedNoDupPerFrame (k + 1) fr hkPre

private theorem closeScope_preserves_ownedDisjoint
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ownedAddressesDisjointAcrossFrames σ' := by
  intro hσ hclose i j fi fj a hij hi hj hai
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  have hiPre : σ.scopes[i + 1]? = some fi := by
    simpa [hσ', hsc] using hi
  have hjPre : σ.scopes[j + 1]? = some fj := by
    simpa [hσ', hsc] using hj
  exact hσ.ownedDisjoint (i + 1) (j + 1) fi fj a
    (by
      intro hEq
      apply hij
      exact Nat.succ.inj hEq)
    hiPre hjPre hai

private theorem closeScope_preserves_refsNotOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    refBindingsNeverOwned σ' := by
  intro hσ hclose k fr x τ a hk href hmem
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  have hkPre : σ.scopes[k + 1]? = some fr := by
    simpa [hσ', hsc] using hk
  exact hσ.refsNotOwned (k + 1) fr x τ a hkPre href hmem

private theorem closeScope_preserves_heapStoredValuesTyped
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ hclose
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  simpa [hσ'] using
    heapInitializedValuesTyped_killLocals
      (σ := { σ with scopes := frs }) (ls := fr0.locals) hσ.heapStoredValuesTyped

private theorem closeScope_preserves_nextFresh
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    nextFreshAgainstOwned σ' := by
  intro hσ hclose
  rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
  rcases hσ.nextFresh with ⟨hheapNone, hlocalsFresh⟩
  have hnextEq : σ'.next = σ.next := by
    simp [hσ']
  refine ⟨?_, ?_⟩
  · have hnotTop : σ.next ∉ fr0.locals := by
      exact hlocalsFresh 0 fr0 (by simp [hsc])
    rw [hnextEq]
    calc
      σ'.heap σ.next = (killLocals { σ with scopes := frs } fr0.locals).heap σ.next := by simp [hσ']
      _ = ({ σ with scopes := frs }).heap σ.next := by
            simp [heap_killLocals_other, hnotTop]
      _ = σ.heap σ.next := by rfl
      _ = none := hheapNone
  · intro k fr hk
    rw [hnextEq]
    have hkPre : σ.scopes[k + 1]? = some fr := by
      simpa [hσ', hsc] using hk
    exact hlocalsFresh (k + 1) fr hkPre

private theorem closeScope_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    (∀ {k x τ a j},
      runtimeFrameBindsRef σ' k x τ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a) := by
  intro hσ hclose k x τ a j hrefPost hjk hownPost
  have hrefPre : runtimeFrameBindsRef σ (k + 1) x τ a :=
    closeScope_reflects_lower_ref_bindings hσ hclose hrefPost
  have hownPre : runtimeFrameOwnsAddress σ (j + 1) a :=
    closeScope_reflects_lower_ownership hσ hclose hownPost
  exact hσ.refTargetsAvoidInnerOwned hrefPre (Nat.succ_lt_succ hjk) hownPre

theorem closeScope_preserves_concrete_state_via_decomposition
    {Γ : TypeEnv} {σ σ' : State} :
    ScopedTypedStateConcrete (pushTypeScope Γ) σ →
    CloseScope σ σ' →
    ScopedTypedStateConcrete Γ σ' := by
  intro hσ hclose
  have hdepth : frameDepthAgreement Γ σ' := by
    rcases closeScope_data hclose with ⟨fr0, frs, hsc, hσ'⟩
    have hlen := hσ.frameDepth
    unfold frameDepthAgreement at hlen ⊢ -- これなら hlen (数式) を展開できる
    simp [pushTypeScope, hsc, hσ'] at hlen ⊢
    exact hlen
  have hexactPost : framewiseDeclBindingExact Γ σ' :=
    closeScope_preserves_framewiseDeclBindingExact hσ.namesExact hclose
  refine
    { frameDepth := hdepth
      namesExact := hexactPost
      shadowing := shadowingCompatible_of_framewiseExact hdepth hexactPost
      objectDeclRealized := closeScope_preserves_objectDeclRealized hσ hclose
      refDeclRealized := closeScope_preserves_refDeclRealized hσ hclose
      objectBindingSound := closeScope_preserves_objectBindingSound hσ hclose
      refBindingSound := closeScope_preserves_refBindingSound hσ hclose
      ownedAddressNamed := closeScope_preserves_ownedAddressNamed hσ hclose
      refsNotOwned := closeScope_preserves_refsNotOwned hσ hclose
      objectsOwned := by
        intro k x τ a hbind
        exact (closeScope_preserves_objectBindingSound hσ hclose hbind).1
      ownedNoDupPerFrame := closeScope_preserves_ownedNoDupPerFrame hσ hclose
      ownedDisjoint := closeScope_preserves_ownedDisjoint hσ hclose
      ownedNamed := by
        intro k a hown
        exact closeScope_preserves_ownedAddressNamed hσ hclose hown
      heapStoredValuesTyped := closeScope_preserves_heapStoredValuesTyped hσ hclose
      nextFresh := closeScope_preserves_nextFresh hσ hclose
      refTargetsAvoidInnerOwned := closeScope_preserves_refTargetsAvoidInnerOwned hσ hclose }

end Cpp
