import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.Realizers
import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.Ownership

namespace Cpp

/-!
# Closure.Transitions.DeclareRef.Preservation

Final assembly for `DeclaresRef` preservation.
The lower layers are split into Shape, RuntimeTransport, Realizers, and Ownership.
-/

theorem declareRef_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    objectBindingSound σ' := by
  intro hσ _ hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  intro k y υ b hbind
  cases hsc : σ.scopes with
  | nil =>
      rcases hbind with ⟨fr, hk, hb⟩
      cases k <;>
        simp [declareRefState, bindTopBinding, hsc] at hk hb
      subst hk
      simp at hb
  | cons fr0 frs =>
      cases k with
      | zero =>
          rcases hbind with ⟨fr, hk, hb⟩
          have hfr : fr =
              { fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z } := by
            simpa [runtimeFrameBindsObject, declareRefState, bindTopBinding, hsc] using hk.symm
          subst hfr
          by_cases hy : y = x
          · subst hy
            simp at hb
          · have hbindOld : runtimeFrameBindsObject σ 0 y υ b := by
              refine ⟨fr0, by simp [hsc], ?_⟩
              simpa [hy] using hb
            rcases hσ.objectBindingSound hbindOld with ⟨hownOld, hliveOld⟩
            refine ⟨?_, ?_⟩
            · simpa [runtimeFrameOwnsAddress, declareRefState, bindTopBinding, hsc] using hownOld
            · simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hliveOld
      | succ j =>
          have hbindOld : runtimeFrameBindsObject σ (j + 1) y υ b := by
            simpa [runtimeFrameBindsObject, declareRefState, bindTopBinding, hsc] using hbind
          rcases hσ.objectBindingSound hbindOld with ⟨hownOld, hliveOld⟩
          refine ⟨?_, ?_⟩
          · simpa [runtimeFrameOwnsAddress, declareRefState, bindTopBinding, hsc] using hownOld
          · simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hliveOld

theorem declareRef_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    refBindingSound σ' := by
  intro hσ _ hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  intro k y υ b hbind
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr0 frs =>
      cases k with
      | zero =>
          rcases hbind with ⟨fr, hk, hb⟩
          have hfr : fr =
              { fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z } := by
            simpa [runtimeFrameBindsRef, declareRefState, bindTopBinding, hsc] using hk.symm
          subst hfr
          by_cases hy : y = x
          · subst hy
            have hs : some (Binding.ref τ a) = some (.ref υ b) := by
              simpa using hb
            injection hs with h_inner
            injection h_inner with hτ_eq hab_eq
            subst hτ_eq
            subst hab_eq
            refine ⟨c, ?_, hty, halive⟩
            simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hheap
          · have hbindOld : runtimeFrameBindsRef σ 0 y υ b := by
              refine ⟨fr0, by simp [hsc], ?_⟩
              simpa [hy] using hb
            simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hσ.refBindingSound hbindOld
      | succ j =>
          have hbindOld : runtimeFrameBindsRef σ (j + 1) y υ b := by
            simpa [runtimeFrameBindsRef, declareRefState, bindTopBinding, hsc] using hbind
          simpa [heapLiveTypedAt, declareRefState, bindTopBinding, hsc] using hσ.refBindingSound hbindOld

theorem declareRef_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    frameDepthAgreement (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hΓ : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hΓ] at hfresh
  | cons Γfr Γrs =>
      cases hσs : σ.scopes with
      | nil =>
          simp [currentScopeFresh, hσs] at hsfresh
      | cons σfr σrs =>
          simpa [frameDepthAgreement, declareTypeRef, insertTopDecl, hΓ,
            declareRefState, bindTopBinding, hσs] using hσ.frameDepth

theorem declareRef_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    shadowingCompatible (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl y d hlookup
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      by_cases hy : y = x
      · subst hy
        have hd : d = .ref τ := by
          rw [lookupDecl_declareTypeRef_self] at hlookup
          exact (Option.some.inj hlookup).symm
        subst hd
        refine ⟨.ref τ a, ?_, ?_⟩
        · simp
        · simp [DeclMatchesBinding]
      · have hlookupOld : lookupDecl Γ y = some d := by
          simpa [lookupDecl_declareTypeRef_other (Γ := Γ) (x := x) (y := y) (τ := τ) hy] using hlookup
        rcases hσ.shadowing y d hlookupOld with ⟨b, hb, hmatch⟩
        refine ⟨b, ?_, hmatch⟩
        simpa [declareRefState, hy] using hb

theorem declareRef_preserves_heapStoredValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a0 : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a0 σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ hdecl
  rcases hdecl with ⟨_, c, hheap, hty, halive, rfl⟩
  intro a c' v hheap' hval
  rw [declareRefState_heap_eq] at hheap'
  exact hσ.heapStoredValuesTyped a c' v hheap' hval

theorem declareRef_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    nextFreshAgainstOwned σ' := by
  intro hσ hdecl
  rcases hdecl with ⟨_, _, _, _, _, rfl⟩
  rcases hσ.nextFresh with ⟨hnext_heap, hnext_locals⟩
  constructor
  · simpa [declareRefState_heap_eq] using hnext_heap
  · intro k fr hk
    cases hsc : σ.scopes with
    | nil =>
      simp [declareRefState, bindTopBinding, hsc] at hk
      cases k with
      | zero =>
          simp at hk
          subst fr
          simp [declareRefState, bindTopBinding, hsc]
      | succ j =>
          simp at hk
    | cons fr0 frs =>
        simp [declareRefState, bindTopBinding, hsc] at hk
        cases k with
        | zero =>
            simp at hk
            subst hk
            simp [declareRefState, bindTopBinding, hsc]
            exact hnext_locals 0 fr0 (by simp [hsc])
        | succ j =>
          simp at hk
          simp [declareRefState, bindTopBinding, hsc]
          exact hnext_locals (j + 1) fr (by simpa [hsc] using hk)

theorem frameDeclBindingExactAt_insertTopRef
    {Γfr : TypeFrame} {σfr : ScopeFrame}
    {x : Ident} {τ : CppType} {a : Nat}
    (hexact : frameDeclBindingExactAt Γfr σfr)
    (hfresh : Γfr.decls x = none) :
    frameDeclBindingExactAt
      { decls := fun y => if y = x then some (.ref τ) else Γfr.decls y }
      { binds := fun y => if y = x then some (.ref τ a) else σfr.binds y,
        locals := σfr.locals } := by
  have hRunFresh : σfr.binds x = none := by
    cases hbx : σfr.binds x with
    | none => rfl
    | some b =>
        rcases hexact.2 x b hbx with ⟨d, hdecl, _⟩
        rw [hfresh] at hdecl
        simp at hdecl
  constructor
  · intro y d hdecl
    by_cases hy : y = x
    · subst hy
      have hd : d = .ref τ := by
        simpa [hfresh] using hdecl.symm
      subst hd
      exact ⟨.ref τ a, by simp, by simp [DeclMatchesBinding]⟩
    · have hdeclOld : Γfr.decls y = some d := by
        simpa [hy] using hdecl
      rcases hexact.1 y d hdeclOld with ⟨b, hb, hmatch⟩
      exact ⟨b, by simpa [hy] using hb, hmatch⟩
  · intro y b hbind
    by_cases hy : y = x
    · subst hy
      have hb : b = .ref τ a := by
        simpa [hRunFresh] using hbind.symm
      subst hb
      exact ⟨.ref τ, by simp, by simp [DeclMatchesBinding]⟩
    · have hbindOld : σfr.binds y = some b := by
        simpa [hy] using hbind
      rcases hexact.2 y b hbindOld with ⟨d, hd, hmatch⟩
      exact ⟨d, by simpa [hy] using hd, hmatch⟩

theorem declareRef_preserves_framewiseDeclBindingExact
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresRef σ τ x a σ' →
    framewiseDeclBindingExact (declareTypeRef Γ x τ) σ' := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨hsfresh, c, hheap, hty, halive, rfl⟩
  cases hΓ : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hΓ] at hfresh
  | cons Γtop Γrest =>
      cases hS : σ.scopes with
      | nil =>
          have hdepth := hσ.frameDepth
          unfold frameDepthAgreement at hdepth
          simp [hΓ, hS] at hdepth
      | cons σtop σrest =>
          intro k Γfr σfr hkΓ hkσ
          cases k with
          | zero =>
              have hExact0 : frameDeclBindingExactAt Γtop σtop :=
                hσ.namesExact 0 Γtop σtop (by simp [hΓ]) (by simp [hS])
              have hTypeFresh0 : Γtop.decls x = none := by
                simpa [currentTypeScopeFresh, hΓ] using hfresh
              have hTop :
                  frameDeclBindingExactAt
                    { decls := fun y => if y = x then some (.ref τ) else Γtop.decls y }
                    { binds := fun y => if y = x then some (.ref τ a) else σtop.binds y,
                      locals := σtop.locals } :=
                frameDeclBindingExactAt_insertTopRef hExact0 hTypeFresh0
              have hΓfr : Γfr = { decls := fun y => if y = x then some (.ref τ) else Γtop.decls y } := by
                simpa [declareTypeRef, insertTopDecl, hΓ] using hkΓ.symm
              have hσfr : σfr = { binds := fun y => if y = x then some (.ref τ a) else σtop.binds y,locals := σtop.locals } := by
                simpa [declareRefState, bindTopBinding, hS] using hkσ.symm
              rw [hΓfr, hσfr]
              exact hTop
          | succ j =>
              have hkΓOld : Γ.scopes[(j + 1)]? = some Γfr := by
                simpa [declareTypeRef, insertTopDecl, hΓ] using hkΓ
              have hkσOld : σ.scopes[(j + 1)]? = some σfr := by
                simpa [declareRefState, bindTopBinding, hS] using hkσ
              exact hσ.namesExact (j + 1) Γfr σfr hkΓOld hkσOld

theorem declareRef_concrete_state_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ' := by
  intro hfresh hσ hdecl
  refine
    { frameDepth := declareRef_preserves_frameDepthAgreement hσ hfresh hdecl
      namesExact := declareRef_preserves_framewiseDeclBindingExact hσ hfresh hdecl
      shadowing := declareRef_preserves_shadowingCompatible hσ hfresh hdecl
      objectDeclRealized := by
        intro k y υ hty
        exact declareRef_objectDeclRealized_of_decomposition hσ hdecl hty
      refDeclRealized := by
        intro k y υ hty
        exact declareRef_refDeclRealized_of_decomposition hfresh hσ hdecl hty
      objectBindingSound := declareRef_preserves_objectBindingSound hσ hfresh hdecl
      refBindingSound := declareRef_preserves_refBindingSound hσ hfresh hdecl
      ownedAddressNamed := by
        intro k addr hown
        exact declareRef_preserves_ownedAddressNamed hσ hdecl hown
      refsNotOwned := declareRef_preserves_refBindingsNeverOwned hσ hdecl
      objectsOwned := declareRef_preserves_allObjectBindingsOwned hσ hdecl
      ownedNoDupPerFrame := declareRef_preserves_ownedNoDupPerFrame hσ hdecl
      ownedDisjoint := declareRef_preserves_ownedDisjointAcrossFrames hσ hdecl
      ownedNamed := by
        intro k addr hown
        exact declareRef_preserves_allOwnedAddressesNamed hσ hdecl k addr hown
      heapStoredValuesTyped := declareRef_preserves_heapStoredValuesTyped hσ hdecl
      nextFresh := declareRef_preserves_nextFreshAgainstOwned hσ hdecl
      refTargetsAvoidInnerOwned := by
        intro k y υ addr j href hjk
        exact declareRef_preserves_refTargetsAvoidInnerOwned hσ hfresh hdecl href hjk }

theorem declares_ref_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {a : Nat} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresRef σ τ x a σ' →
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) σ' := by
  intro hfresh hσ hdecl
  exact declareRef_concrete_state_of_decomposition hfresh hσ hdecl

end Cpp
