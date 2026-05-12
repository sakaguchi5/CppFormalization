import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteDeclRealization
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteOwnershipAssembly
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteExactnessTransport

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteFullAssembly

`ScopedTypedStateConcreteOwnership` の bundle assembly の上に、
`kernel` と `heapStoredValuesTyped` を足して
full `ScopedTypedStateConcrete` を再構成する層。

今回の方針:
- ownership は直前の assembly をそのまま使う。
- `frameDepth` / `shadowing` / `declRealized` は declaration ごとに transport する。
- object 宣言では新しい owner / heap cell をその場で作る。
- ref 宣言では ownership は変えず、new ref decl の live target だけを外部仮定で受ける。
- recomputed-cursor object 宣言でも、full state は strong fields だけで組み立てる。
-/
/-!
Exactness / lookup / frame-depth transport lemmas are provided by
`StateInvariantConcreteExactnessTransport`.  This file is now only the
full concrete-state assembly layer.
-/

namespace DeclareObjectReadyStrong

theorem objectBindingSound_declareObjectState_new
    {σ : State} {x : Ident}
    {τ : CppType} {ov : Option Value}
    {k : Nat} {y : Ident} {υ : CppType} {a : Nat}
    (hnew : k = 0 ∧ y = x ∧ υ = τ ∧ a = σ.next) :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k a ∧
    heapLiveTypedAt (declareObjectState σ τ x ov) a υ := by
  rcases hnew with ⟨hk, hxy, hυτ, hanext⟩
  constructor
  · rw [hk, hanext]
    exact runtimeFrameOwnsAddress_declareObjectState_zero_next (σ := σ) (ov := ov) (x := _) (τ := _)
  · rw [hυτ, hanext]
    exact heapLiveTypedAt_declareObjectState_self (σ := σ) (ov := ov) (x := _) (τ := _)

theorem kernel_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcreteKernel (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  refine
    { frameDepth := frameDepthAgreement_declareTypeObject_declareObjectState h.concrete.frameDepth
      shadowing := shadowingCompatible_declareTypeObject_declareObjectState h.concrete.shadowing
      namesExact :=framewiseDeclBindingExact_declareTypeObject_declareObjectState_from_topFrameFresh
        h.concrete.frameDepth h.concrete.namesExact hΓ0 (h.typeFresh _ hΓ0) (h.topFrameFresh hΓ0)
      objectDeclRealized := objectDeclRealized_after_declareObjectState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov)
      refDeclRealized := refDeclRealized_after_declareObjectState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov)
      objectBindingSound := by
        intro k y υ a hbind
        rcases runtimeFrameBindsObject_declareObjectState_cases hbind with
          hnew | hold
        ·
          exact objectBindingSound_declareObjectState_new  hnew
        · rcases h.concrete.objectBindingSound hold with ⟨hownOld, hliveOld⟩
          have hane : a ≠ σ.next :=
            runtimeFrameOwnsAddress_ne_next_of_nextFresh h.concrete.nextFresh hownOld
          exact ⟨
            runtimeFrameOwnsAddress_declareObjectState_forward hownOld,
            heapLiveTypedAt_declareObjectState_of_ne hane hliveOld⟩
      refBindingSound := by
        intro k y υ a hbind
        have hbindOld :
            runtimeFrameBindsRef σ k y υ a :=
          runtimeFrameBindsRef_declareObjectState_backward hbind
        have hliveOld : heapLiveTypedAt σ a υ :=
          h.concrete.refBindingSound hbindOld
        have hane : a ≠ σ.next :=
          heapLiveTypedAt_ne_next_of_nextFresh h.concrete.nextFresh hliveOld
        exact
          heapLiveTypedAt_declareObjectState_of_ne hane hliveOld }

 theorem concrete_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value}
    (hov : OptionValueCompat ov τ)
    (hnextSucc : freshAddrAgainstOwned σ (σ.next + 1)) :
    ScopedTypedStateConcrete (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  let hker := kernel_after_declareObjectState
    (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov)
  let hown := ownership_after_declareObjectState
    (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hnextSucc
  refine
    { frameDepth := hker.frameDepth
      shadowing := hker.shadowing
      namesExact := hker.namesExact
      objectDeclRealized := hker.objectDeclRealized
      refDeclRealized := hker.refDeclRealized
      ownedAddressNamed := hown.ownedAddressNamed
      refsNotOwned := hown.refsNotOwned
      objectsOwned := hown.objectsOwned
      ownedNoDupPerFrame := hown.ownedNoDupPerFrame
      ownedDisjoint := hown.ownedDisjoint
      ownedNamed := hown.ownedNamed
      objectBindingSound := hker.objectBindingSound
      refBindingSound := hker.refBindingSound
      heapStoredValuesTyped :=
        heapInitializedValuesTyped_declareObjectState_of_optionCompat
          h.concrete.heapStoredValuesTyped hov
      nextFresh := hown.nextFresh
      refTargetsAvoidInnerOwned := hown.refTargetsAvoidInnerOwned }

end DeclareObjectReadyStrong

namespace DeclareRefReadyStrong

theorem kernel_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    (haLive : heapLiveTypedAt σ a τ) :
    ScopedTypedStateConcreteKernel (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  refine
    { frameDepth := frameDepthAgreement_declareTypeRef_declareRefState
        (a := a) h.concrete.frameDepth
      shadowing := shadowingCompatible_declareTypeRef_declareRefState
        (a := a) h.concrete.shadowing
      namesExact :=framewiseDeclBindingExact_declareTypeRef_declareRefState_from_topFrameFresh
        h.concrete.frameDepth h.concrete.namesExact hΓ0 (h.typeFresh _ hΓ0) (h.topFrameFresh hΓ0)
      objectDeclRealized := objectDeclRealized_after_declareRefState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a)
      refDeclRealized := refDeclRealized_after_declareRefState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) haLive
      objectBindingSound := by
        intro k y υ addr hbind
        have hbindOld :
            runtimeFrameBindsObject σ k y υ addr :=
          runtimeFrameBindsObject_declareRefState_backward hbind
        rcases h.concrete.objectBindingSound hbindOld with ⟨hownOld, hliveOld⟩
        exact ⟨
          runtimeFrameOwnsAddress_declareRefState_forward hownOld,
          (heapLiveTypedAt_declareRefState_iff).2 hliveOld⟩
      refBindingSound := by
        intro k y υ addr hbind
        rcases runtimeFrameBindsRef_declareRefState_cases hbind with
          hnew | hold
        · rcases hnew with ⟨rfl, rfl, rfl, rfl⟩
          exact (heapLiveTypedAt_declareRefState_iff (σ := σ)).2 haLive
        · have hliveOld : heapLiveTypedAt σ addr υ :=
            h.concrete.refBindingSound hold
          exact
            (heapLiveTypedAt_declareRefState_iff).2 hliveOld }

 theorem concrete_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    (haLive : heapLiveTypedAt σ a τ) :
    ScopedTypedStateConcrete (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  let hker := kernel_after_declareRefState
    (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) haLive
  let hown := ownership_after_declareRefState
    (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a)
  refine
    { frameDepth := hker.frameDepth
      shadowing := hker.shadowing
      namesExact := hker.namesExact
      objectDeclRealized := hker.objectDeclRealized
      refDeclRealized := hker.refDeclRealized
      ownedAddressNamed := hown.ownedAddressNamed
      refsNotOwned := hown.refsNotOwned
      objectsOwned := hown.objectsOwned
      ownedNoDupPerFrame := hown.ownedNoDupPerFrame
      ownedDisjoint := hown.ownedDisjoint
      ownedNamed := hown.ownedNamed
      objectBindingSound := hker.objectBindingSound
      refBindingSound := hker.refBindingSound
      heapStoredValuesTyped :=
        (heapInitializedValuesTyped_declareRefState).2 h.concrete.heapStoredValuesTyped
      nextFresh := hown.nextFresh
      refTargetsAvoidInnerOwned := hown.refTargetsAvoidInnerOwned }

end DeclareRefReadyStrong

end Cpp

namespace Cpp

namespace DeclareObjectReadyRecomputed

theorem kernel_after_declareObjectStateWithNext
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {Γfr : TypeFrame}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    ScopedTypedStateConcreteKernel
      (declareTypeObject Γ x τ)
      (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  refine
    { frameDepth :=
        frameDepthAgreement_declareTypeObject_declareObjectStateWithNext
          (Γ := Γ) (σ := σ) (x := x) (τ := τ) (ov := ov) (aNext := h.cursor.addr)
          h.ready.concrete.frameDepth
      shadowing :=
        shadowingCompatible_declareTypeObject_declareObjectStateWithNext
          (Γ := Γ) (σ := σ) (x := x) (τ := τ) (ov := ov) (aNext := h.cursor.addr)
          h.ready.concrete.shadowing
      namesExact := framewiseDeclBindingExact_declareTypeObject_declareObjectStateWithNext
        h.ready.concrete.frameDepth h.ready.concrete.namesExact hΓ0 (h.ready.typeFresh _ hΓ0) (h.ready.topFrameFresh hΓ0)
      objectDeclRealized :=
        objectDeclRealized_after_declareObjectStateWithNext
          (h := h) (hΓ0 := hΓ0)
      refDeclRealized :=
        refDeclRealized_after_declareObjectStateWithNext
          (h := h) (hΓ0 := hΓ0)
      objectBindingSound := by
        intro k y υ a hbind
        rcases runtimeFrameBindsObject_declareObjectStateWithNext_cases hbind with hnew | hold
        · rcases hnew with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨
            declareObjectStateWithNext_api_runtimeFrameOwnsAddress_zero_new,
            heapLiveTypedAt_declareObjectStateWithNext_self⟩
        · rcases h.ready.concrete.objectBindingSound hold with ⟨hownOld, hliveOld⟩
          exact ownedAndLive_declareObjectStateWithNext_of_oldOwned
            (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := h.cursor.addr)
            h.ready.concrete.nextFresh hownOld hliveOld
      refBindingSound := by
        intro k y υ a hbind
        have hbindOld : runtimeFrameBindsRef σ k y υ a :=
          runtimeFrameBindsRef_declareObjectStateWithNext_backward hbind
        have hliveOld : heapLiveTypedAt σ a υ :=
          h.ready.concrete.refBindingSound hbindOld
        exact heapLiveTypedAt_declareObjectStateWithNext_of_oldLive
          (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := h.cursor.addr)
          h.ready.concrete.nextFresh hliveOld }

theorem concrete_after_declareObjectStateWithNext
    {Γ : TypeEnv} {σ : State} {x : Ident}
    {Γfr : TypeFrame}
    {τ : CppType} {ov : Option Value}
    (h : DeclareObjectReadyRecomputed Γ σ x τ ov)
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    (hov : OptionValueCompat ov τ) :
    ScopedTypedStateConcrete
      (declareTypeObject Γ x τ)
      (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
  let hker :=
    kernel_after_declareObjectStateWithNext
      (h := h) (hΓ0 := hΓ0)
  let hown :=
    DeclareObjectReadyRecomputed.ownership_after_declareObjectStateWithNext
      (h := h) (hΓ0 := hΓ0)
  have hheapNew :
      heapInitializedValuesTyped
        (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
    exact heapInitializedValuesTyped_declareObjectStateWithNext_of_optionCompat
      (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := h.cursor.addr)
      h.ready.concrete.heapStoredValuesTyped hov
  refine
    { frameDepth := hker.frameDepth
      shadowing := hker.shadowing
      namesExact := hker.namesExact
      objectDeclRealized := hker.objectDeclRealized
      refDeclRealized := hker.refDeclRealized
      objectBindingSound := hker.objectBindingSound
      refBindingSound := hker.refBindingSound
      ownedAddressNamed := hown.ownedAddressNamed
      refsNotOwned := hown.refsNotOwned
      objectsOwned := hown.objectsOwned
      ownedNoDupPerFrame := hown.ownedNoDupPerFrame
      ownedDisjoint := hown.ownedDisjoint
      ownedNamed := hown.ownedNamed
      heapStoredValuesTyped := hheapNew
      nextFresh := hown.nextFresh
      refTargetsAvoidInnerOwned := hown.refTargetsAvoidInnerOwned }

end DeclareObjectReadyRecomputed
end Cpp

