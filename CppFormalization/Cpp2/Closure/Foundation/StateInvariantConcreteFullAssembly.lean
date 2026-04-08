import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteDeclRealization
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteOwnershipAssembly

namespace Cpp

/-!
# Closure.Foundation.StateInvariantConcreteFullAssembly

`ScopedTypedStateConcreteOwnership` の bundle assembly の上に、
`kernel`・`heapStoredValuesTyped`・legacy placeholder を足して
full `ScopedTypedStateConcrete` を再構成する層。

今回の方針:
- ownership は直前の assembly をそのまま使う。
- `frameDepth` / `shadowing` / `declRealized` は declaration ごとに transport する。
- object 宣言では新しい owner / heap cell をその場で作る。
- ref 宣言では ownership は変えず、new ref decl の live target だけを外部仮定で受ける。
-/

section TypeEnvLocalLemmas

@[simp] theorem lookupDecl_insertTopDecl_self
    (Γ : TypeEnv) (x : Ident) (d : DeclInfo) :
    lookupDecl (insertTopDecl Γ x d) x = some d := by
  unfold lookupDecl insertTopDecl lookupDeclFrames
  cases hsc : Γ.scopes with
  | nil => simp
  | cons fr frs => simp

@[simp] theorem lookupDecl_insertTopDecl_other
    (Γ : TypeEnv) {x y : Ident} (d : DeclInfo) (hxy : y ≠ x) :
    lookupDecl (insertTopDecl Γ x d) y = lookupDecl Γ y := by
  unfold lookupDecl insertTopDecl lookupDeclFrames
  cases hsc : Γ.scopes with
  | nil => simp [hxy, lookupDeclFrames]
  | cons fr frs => simp [hxy]

@[simp] theorem lookupDecl_declareTypeObject_self
    (Γ : TypeEnv) (x : Ident) (τ : CppType) :
    lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by
  simp [declareTypeObject]

@[simp] theorem lookupDecl_declareTypeObject_other
    (Γ : TypeEnv) {x y : Ident} (τ : CppType) (hxy : y ≠ x) :
    lookupDecl (declareTypeObject Γ x τ) y = lookupDecl Γ y := by
  simp [declareTypeObject, hxy]

@[simp] theorem lookupDecl_declareTypeRef_self
    (Γ : TypeEnv) (x : Ident) (τ : CppType) :
    lookupDecl (declareTypeRef Γ x τ) x = some (.ref τ) := by
  simp [declareTypeRef]

@[simp] theorem lookupDecl_declareTypeRef_other
    (Γ : TypeEnv) {x y : Ident} (τ : CppType) (hxy : y ≠ x) :
    lookupDecl (declareTypeRef Γ x τ) y = lookupDecl Γ y := by
  simp [declareTypeRef, hxy]

@[simp] theorem declareTypeObject_scopes_succ
    {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} :
    (declareTypeObject Γ x τ).scopes[k.succ]? = Γ.scopes[k.succ]? := by
  cases hsc : Γ.scopes <;> simp [declareTypeObject, insertTopDecl, hsc]

@[simp] theorem declareTypeRef_scopes_succ
    {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} :
    (declareTypeRef Γ x τ).scopes[k.succ]? = Γ.scopes[k.succ]? := by
  cases hsc : Γ.scopes <;> simp [declareTypeRef, insertTopDecl, hsc]

@[simp] theorem frameDepthAgreement_declareTypeObject_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    frameDepthAgreement Γ σ →
    frameDepthAgreement (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  intro hdepth
  unfold frameDepthAgreement at *
  cases hG : Γ.scopes <;> cases hS : σ.scopes <;>
    simp [declareTypeObject, insertTopDecl, declareObjectState, recordLocal, bindTopBinding,
      writeHeap, hG, hS] at *
  exact hdepth

@[simp] theorem frameDepthAgreement_declareTypeRef_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    frameDepthAgreement Γ σ →
    frameDepthAgreement (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  intro hdepth
  unfold frameDepthAgreement at *
  cases hG : Γ.scopes <;> cases hS : σ.scopes <;>
    simp [declareTypeRef, insertTopDecl, declareRefState, bindTopBinding, hG, hS] at *
  exact hdepth

 theorem shadowingCompatible_declareTypeObject_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    shadowingCompatible Γ σ →
    shadowingCompatible (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  intro hshadow
  intro y d hdecl
  by_cases hy : y = x
  · subst y
    have hd : d = .object τ := by
      rw [lookupDecl_declareTypeObject_self] at hdecl
      exact Option.some.inj hdecl.symm
    subst d
    refine ⟨.object τ σ.next, ?_, ?_⟩
    · simp [lookupBinding_declareObjectState_self]
    · simp [DeclMatchesBinding]
  · have hdeclOld : lookupDecl Γ y = some d := by
      simpa [lookupDecl_declareTypeObject_other (Γ := Γ) (τ := τ) hy] using hdecl
    rcases hshadow y d hdeclOld with ⟨b, hb, hmatch⟩
    refine ⟨b, ?_, hmatch⟩
    simpa [lookupBinding_declareObjectState_other (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) hy] using hb

 theorem shadowingCompatible_declareTypeRef_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    shadowingCompatible Γ σ →
    shadowingCompatible (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  intro hshadow
  intro y d hdecl
  by_cases hy : y = x
  · subst y
    have hd : d = .ref τ := by
      rw [lookupDecl_declareTypeRef_self] at hdecl
      exact Option.some.inj hdecl.symm
    subst d
    refine ⟨.ref τ a, ?_, ?_⟩
    · simp [lookupBinding_declareRefState_self]
    · simp [DeclMatchesBinding]
  · have hdeclOld : lookupDecl Γ y = some d := by
      simpa [lookupDecl_declareTypeRef_other (Γ := Γ) (τ := τ) hy] using hdecl
    rcases hshadow y d hdeclOld with ⟨b, hb, hmatch⟩
    refine ⟨b, ?_, hmatch⟩
    simpa [lookupBinding_declareRefState_other (σ := σ) (τ := τ) (x := x) (y := y) (a := a) hy] using hb

end TypeEnvLocalLemmas

namespace DeclareObjectReadyStrong
 theorem kernel_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcreteKernel (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  refine
    { frameDepth := frameDepthAgreement_declareTypeObject_declareObjectState
        (Γ := Γ) (σ := σ) (x := x) (τ := τ) (ov := ov) h.concrete.frameDepth
      shadowing := shadowingCompatible_declareTypeObject_declareObjectState
        (Γ := Γ) (σ := σ) (x := x) (τ := τ) (ov := ov) h.concrete.shadowing
      objectDeclRealized := objectDeclRealized_after_declareObjectState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov)
      refDeclRealized := refDeclRealized_after_declareObjectState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) }

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
      objectDeclRealized := hker.objectDeclRealized
      refDeclRealized := hker.refDeclRealized
      ownedAddressNamed := hown.ownedAddressNamed
      refsNotOwned := hown.refsNotOwned
      objectsOwned := hown.objectsOwned
      ownedNoDupPerFrame := hown.ownedNoDupPerFrame
      ownedDisjoint := hown.ownedDisjoint
      ownedNamed := hown.ownedNamed
      heapStoredValuesTyped :=
        heapInitializedValuesTyped_declareObjectState_of_optionCompat
          (σ := σ) (τ := τ) (x := x) (ov := ov)
          h.concrete.heapStoredValuesTyped hov
      initializedValuesTyped := objectBindingsInitializedTypedWeak_trivial _
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
        (Γ := Γ) (σ := σ) (x := x) (τ := τ) (a := a) h.concrete.frameDepth
      shadowing := shadowingCompatible_declareTypeRef_declareRefState
        (Γ := Γ) (σ := σ) (x := x) (τ := τ) (a := a) h.concrete.shadowing
      objectDeclRealized := objectDeclRealized_after_declareRefState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a)
      refDeclRealized := refDeclRealized_after_declareRefState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) haLive }

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
      objectDeclRealized := hker.objectDeclRealized
      refDeclRealized := hker.refDeclRealized
      ownedAddressNamed := hown.ownedAddressNamed
      refsNotOwned := hown.refsNotOwned
      objectsOwned := hown.objectsOwned
      ownedNoDupPerFrame := hown.ownedNoDupPerFrame
      ownedDisjoint := hown.ownedDisjoint
      ownedNamed := hown.ownedNamed
      heapStoredValuesTyped :=
        (heapInitializedValuesTyped_declareRefState
          (σ := σ) (τ := τ) (x := x) (a := a)).2 h.concrete.heapStoredValuesTyped
      initializedValuesTyped := objectBindingsInitializedTypedWeak_trivial _
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
  let hold :=
    DeclareObjectReadyStrong.kernel_after_declareObjectState
      (h := h.ready) (hΓ0 := hΓ0) (τ := τ) (ov := ov)
  refine
    { frameDepth := by
        unfold frameDepthAgreement at *
        simpa [scopes_declareObjectStateWithNext_eq_old] using hold.frameDepth
      shadowing := by
        intro y d hdecl
        rcases hold.shadowing y d hdecl with ⟨b, hb, hmatch⟩
        refine ⟨b, ?_, hmatch⟩
        simpa [lookupBinding, scopes_declareObjectStateWithNext_eq_old] using hb
      objectDeclRealized :=
        objectDeclRealized_after_declareObjectStateWithNext
          (h := h) (hΓ0 := hΓ0)
      refDeclRealized :=
        refDeclRealized_after_declareObjectStateWithNext
          (h := h) (hΓ0 := hΓ0) }

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
  have hheapOld :
      heapInitializedValuesTyped (declareObjectState σ τ x ov) := by
    exact heapInitializedValuesTyped_declareObjectState_of_optionCompat
      (σ := σ) (τ := τ) (x := x) (ov := ov)
      h.ready.concrete.heapStoredValuesTyped hov
  have hheapNew :
      heapInitializedValuesTyped
        (declareObjectStateWithNext σ τ x ov h.cursor.addr) := by
    simpa [heapInitializedValuesTyped, heap_declareObjectStateWithNext_eq_old] using hheapOld
  refine
    { frameDepth := hker.frameDepth
      shadowing := hker.shadowing
      objectDeclRealized := hker.objectDeclRealized
      refDeclRealized := hker.refDeclRealized
      ownedAddressNamed := hown.ownedAddressNamed
      refsNotOwned := hown.refsNotOwned
      objectsOwned := hown.objectsOwned
      ownedNoDupPerFrame := hown.ownedNoDupPerFrame
      ownedDisjoint := hown.ownedDisjoint
      ownedNamed := hown.ownedNamed
      heapStoredValuesTyped := hheapNew
      initializedValuesTyped := objectBindingsInitializedTypedWeak_trivial _
      nextFresh := hown.nextFresh
      refTargetsAvoidInnerOwned := hown.refTargetsAvoidInnerOwned }

end DeclareObjectReadyRecomputed
end Cpp
