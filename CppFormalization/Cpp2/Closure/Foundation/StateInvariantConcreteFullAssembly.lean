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
-
- type-env lookup 系と decl transport 系を分離する。
- `k = 0` の nonempty / top-frame 同定 / old-decl 引き戻しを局所 API に吸う。
- `k = succ` の引き戻しは `*_succ_iff` で統一する。
-/

section TypeEnvLookupLocalLemmas

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

end TypeEnvLookupLocalLemmas

section TypeEnvDeclTransportLocalLemmas

 theorem typeEnv_scopes_cons_of_zero_lookup
    {Γ : TypeEnv} {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr) :
    ∃ fr0 frs, Γ.scopes = fr0 :: frs := by
  cases hsc : Γ.scopes with
  | nil =>
      simp [hsc] at hΓ0
  | cons fr0 frs =>
      exact ⟨fr0, frs, rfl⟩

@[simp] theorem declareTypeObject_scopes_succ
    {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} :
    (declareTypeObject Γ x τ).scopes[k.succ]? = Γ.scopes[k.succ]? := by
  cases hsc : Γ.scopes <;> simp [declareTypeObject, insertTopDecl, hsc]

@[simp] theorem declareTypeRef_scopes_succ
    {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} :
    (declareTypeRef Γ x τ).scopes[k.succ]? = Γ.scopes[k.succ]? := by
  cases hsc : Γ.scopes <;> simp [declareTypeRef, insertTopDecl, hsc]

 theorem declareTypeObject_lookup_zero_frame_of_cons
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {fr0 : TypeFrame} {frs : List TypeFrame}
    (hsc : Γ.scopes = fr0 :: frs)
    {Γfr' : TypeFrame}
    (hk : (declareTypeObject Γ x τ).scopes[0]? = some Γfr') :
    Γfr' =
      { fr0 with
        decls := fun y => if y = x then some (.object τ) else fr0.decls y } := by
  have htop :
      (declareTypeObject Γ x τ).scopes[0]? =
        some
          { fr0 with
            decls := fun y => if y = x then some (.object τ) else fr0.decls y } := by
    simp [declareTypeObject, insertTopDecl, hsc]
  exact Option.some.inj (hk.symm.trans htop)

 theorem declareTypeRef_lookup_zero_frame_of_cons
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {fr0 : TypeFrame} {frs : List TypeFrame}
    (hsc : Γ.scopes = fr0 :: frs)
    {Γfr' : TypeFrame}
    (hk : (declareTypeRef Γ x τ).scopes[0]? = some Γfr') :
    Γfr' =
      { fr0 with
        decls := fun y => if y = x then some (.ref τ) else fr0.decls y } := by
  have htop :
      (declareTypeRef Γ x τ).scopes[0]? =
        some
          { fr0 with
            decls := fun y => if y = x then some (.ref τ) else fr0.decls y } := by
    simp [declareTypeRef, insertTopDecl, hsc]
  exact Option.some.inj (hk.symm.trans htop)

@[simp] theorem typeFrameDeclObject_declareTypeObject_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclObject (declareTypeObject Γ x τ) k.succ y υ ↔
      typeFrameDeclObject Γ k.succ y υ := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩

@[simp] theorem typeFrameDeclRef_declareTypeObject_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclRef (declareTypeObject Γ x τ) k.succ y υ ↔
      typeFrameDeclRef Γ k.succ y υ := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩

@[simp] theorem typeFrameDeclObject_declareTypeRef_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclObject (declareTypeRef Γ x τ) k.succ y υ ↔
      typeFrameDeclObject Γ k.succ y υ := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩

@[simp] theorem typeFrameDeclRef_declareTypeRef_succ_iff
    {Γ : TypeEnv} {x y : Ident} {τ υ : CppType} {k : Nat} :
    typeFrameDeclRef (declareTypeRef Γ x τ) k.succ y υ ↔
      typeFrameDeclRef Γ k.succ y υ := by
  constructor <;> intro h
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩
  · rcases h with ⟨fr, hk, hb⟩
    exact ⟨fr, by simpa using hk, hb⟩

 theorem typeFrameDeclObject_declareTypeObject_zero_old_of_ne
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType}
    {fr0 : TypeFrame} {frs : List TypeFrame}
    (hsc : Γ.scopes = fr0 :: frs)
    (hx' : x' ≠ x) :
    typeFrameDeclObject (declareTypeObject Γ x τ) 0 x' τ' →
      typeFrameDeclObject Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  rcases declareTypeObject_lookup_zero_frame_of_cons
      (Γ := Γ) (x := x) (τ := τ) (fr0 := fr0) (frs := frs) hsc hk with rfl
  exact ⟨fr0, by simp [hsc], by simpa [hx'] using hb⟩

 theorem typeFrameDeclRef_declareTypeRef_zero_old_of_ne
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType}
    {fr0 : TypeFrame} {frs : List TypeFrame}
    (hsc : Γ.scopes = fr0 :: frs)
    (hx' : x' ≠ x) :
    typeFrameDeclRef (declareTypeRef Γ x τ) 0 x' τ' →
      typeFrameDeclRef Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  rcases declareTypeRef_lookup_zero_frame_of_cons
      (Γ := Γ) (x := x) (τ := τ) (fr0 := fr0) (frs := frs) hsc hk with rfl
  exact ⟨fr0, by simp [hsc], by simpa [hx'] using hb⟩

 theorem typeFrameDeclRef_declareTypeObject_zero_old
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType}
    {fr0 : TypeFrame} {frs : List TypeFrame}
    (hsc : Γ.scopes = fr0 :: frs) :
    typeFrameDeclRef (declareTypeObject Γ x τ) 0 x' τ' →
      typeFrameDeclRef Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  rcases declareTypeObject_lookup_zero_frame_of_cons
      (Γ := Γ) (x := x) (τ := τ) (fr0 := fr0) (frs := frs) hsc hk with rfl
  have hx' : x' ≠ x := by
    intro hEq
    subst x'
    simp at hb
  exact ⟨fr0, by simp [hsc], by simpa [hx'] using hb⟩

 theorem typeFrameDeclObject_declareTypeRef_zero_old
    {Γ : TypeEnv} {x x' : Ident} {τ τ' : CppType}
    {fr0 : TypeFrame} {frs : List TypeFrame}
    (hsc : Γ.scopes = fr0 :: frs) :
    typeFrameDeclObject (declareTypeRef Γ x τ) 0 x' τ' →
      typeFrameDeclObject Γ 0 x' τ' := by
  intro hdecl
  rcases hdecl with ⟨Γfr', hk, hb⟩
  rcases declareTypeRef_lookup_zero_frame_of_cons
      (Γ := Γ) (x := x) (τ := τ) (fr0 := fr0) (frs := frs) hsc hk with rfl
  have hx' : x' ≠ x := by
    intro hEq
    subst x'
    simp at hb
  exact ⟨fr0, by simp [hsc], by simpa [hx'] using hb⟩

end TypeEnvDeclTransportLocalLemmas

section StateTransportLocalLemmas

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

@[simp] theorem heapLiveTypedAt_declareRefState_iff
    {σ : State} {τ : CppType} {x : Ident} {r : Nat} {a : Nat} {υ : CppType} :
    heapLiveTypedAt (declareRefState σ τ x r) a υ ↔ heapLiveTypedAt σ a υ := by
  constructor <;> intro h
  · rcases h with ⟨c, hc, hty, halive⟩
    refine ⟨c, ?_, hty, halive⟩
    simpa [declareRefState] using hc
  · rcases h with ⟨c, hc, hty, halive⟩
    refine ⟨c, ?_, hty, halive⟩
    simpa [declareRefState] using hc

 theorem heapLiveTypedAt_declareObjectState_of_ne
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    {a : Nat} {υ : CppType} :
    a ≠ σ.next →
    heapLiveTypedAt σ a υ →
    heapLiveTypedAt (declareObjectState σ τ x ov) a υ := by
  intro hne hlive
  rcases hlive with ⟨c, hc, hty, halive⟩
  refine ⟨c, ?_, hty, halive⟩
  simpa [declareObjectState_heap_other (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) hne] using hc

@[simp] theorem heapLiveTypedAt_declareObjectState_self
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    heapLiveTypedAt (declareObjectState σ τ x ov) σ.next τ := by
  refine ⟨{ ty := τ, value := ov, alive := true }, ?_, rfl, rfl⟩
  simp

 theorem runtimeFrameOwnsAddress_ne_next_of_nextFresh
    {σ : State} {k : Nat} {a : Nat} :
    nextFreshAgainstOwned σ →
    runtimeFrameOwnsAddress σ k a →
    a ≠ σ.next := by
  intro hfresh hown
  rcases hfresh with ⟨_, hlocals⟩
  rcases hown with ⟨fr, hk, ha⟩
  intro hEq
  subst a
  exact hlocals k fr hk ha

 theorem heapLiveTypedAt_ne_next_of_nextFresh
    {σ : State} {a : Nat} {τ : CppType} :
    nextFreshAgainstOwned σ →
    heapLiveTypedAt σ a τ →
    a ≠ σ.next := by
  intro hfresh hlive
  rcases hfresh with ⟨hheapNone, _⟩
  rcases hlive with ⟨c, hc, _, _⟩
  intro hEq
  subst a
  rw [hheapNone] at hc
  simp at hc

 theorem runtimeFrameBindsRef_top_name_ne_declared_of_topFresh
    {σ : State} {x y : Ident} {fr0 : ScopeFrame} {frs : List ScopeFrame}
    {υ : CppType} {addr : Nat}
    (hfresh : topFrameBindingFresh σ x)
    (hsc : σ.scopes = fr0 :: frs)
    (hb : fr0.binds y = some (.ref υ addr)) :
    y ≠ x := by
  intro hEq
  subst y
  rw [topFrameBindingFresh_zero_of_cons (σ := σ) (x := x) (fr0 := fr0) (frs := frs) hfresh hsc] at hb
  simp at hb

 theorem runtimeFrameBindsRef_declareRefState_zero_new
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    {fr : ScopeFrame}
    (hk : (declareRefState σ τ x a).scopes[0]? = some fr) :
    runtimeFrameBindsRef (declareRefState σ τ x a) 0 x τ a := by
  refine ⟨fr, hk, ?_⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [declareRefState, scopes_bindTopBinding, hsc] at hk
      subst fr
      simp
  | cons fr0 frs =>
      rcases declareRefState_lookup_zero_frame_of_cons
        (σ := σ) (τ := τ) (x := x) (a := a)
        (fr0 := fr0) (frs := frs) hsc hk with rfl
      simp

 theorem runtimeFrameBindsRef_declareRefState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef σ k y υ addr →
    runtimeFrameBindsRef (declareRefState σ τ x a) k y υ addr := by
  intro href
  rcases href with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero => simp [hsc] at hk
      | succ k => simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [hsc] at hk
          subst fr
          have hyx : y ≠ x :=
            runtimeFrameBindsRef_top_name_ne_declared_of_topFresh
              (σ := σ) (x := x) (y := y) (fr0 := fr0) (frs := frs)
              (υ := υ) (addr := addr) hfresh hsc hb
          refine ⟨
            { fr0 with binds := fun z => if z = x then some (.ref τ a) else fr0.binds z },
            ?_, ?_⟩
          · simp [declareRefState, scopes_bindTopBinding, hsc]
          · simpa [hyx] using hb
      | succ k =>
          refine ⟨fr, ?_, hb⟩
          exact (declareRefState_lookup_succ_iff
            (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (fr := fr)).2 hk

 theorem runtimeFrameBindsRef_declareObjectState_forward_of_topFresh
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hfresh : topFrameBindingFresh σ x)
    {k : Nat} {y : Ident} {υ : CppType} {addr : Nat} :
    runtimeFrameBindsRef σ k y υ addr →
    runtimeFrameBindsRef (declareObjectState σ τ x ov) k y υ addr := by
  intro href
  rcases href with ⟨fr, hk, hb⟩
  cases hsc : σ.scopes with
  | nil =>
      cases k with
      | zero => simp [hsc] at hk
      | succ k => simp [hsc] at hk
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [hsc] at hk
          subst fr
          have hyx : y ≠ x :=
            runtimeFrameBindsRef_top_name_ne_declared_of_topFresh
              (σ := σ) (x := x) (y := y) (fr0 := fr0) (frs := frs)
              (υ := υ) (addr := addr) hfresh hsc hb
          refine ⟨
            { fr0 with
              binds := fun z => if z = x then some (.object τ σ.next) else fr0.binds z,
              locals := σ.next :: fr0.locals },
            ?_, ?_⟩
          · simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hsc]
          · simpa [hyx] using hb
      | succ k =>
          refine ⟨fr, ?_, hb⟩
          exact (declareObjectState_lookup_succ_iff
            (σ := σ) (τ := τ) (x := x) (ov := ov) (k := k) (fr := fr)).2 hk

 theorem shadowingCompatible_declareTypeObject_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    shadowingCompatible Γ σ →
    shadowingCompatible (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  intro hshadow
  intro y d hdecl
  by_cases hy : y = x
  · subst y
    rw [lookupDecl_declareTypeObject_self] at hdecl
    injection hdecl with hd
    subst hd
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
    rw [lookupDecl_declareTypeRef_self] at hdecl
    injection hdecl with hd
    subst hd
    refine ⟨.ref τ a, ⟨?_, by simp [DeclMatchesBinding]⟩⟩
    unfold lookupBinding declareRefState bindTopBinding
    cases hsc : σ.scopes with
    | nil => simp [lookupBindingFrames]
    | cons fr frs => simp [lookupBindingFrames]
  · have hdeclOld : lookupDecl Γ y = some d := by
      simpa [lookupDecl_declareTypeRef_other (Γ := Γ) (τ := τ) hy] using hdecl
    rcases hshadow y d hdeclOld with ⟨b, hb, hmatch⟩
    refine ⟨b, ?_, hmatch⟩
    simpa [lookupBinding_declareRefState_other (σ := σ) (τ := τ) (x := x) (y := y) (a := a) hy] using hb

end StateTransportLocalLemmas

namespace DeclareObjectReadyStrong

theorem transport_old_object_realization_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclObject Γ k x' τ') :
    ∃ a,
      runtimeFrameBindsObject (declareObjectState σ τ x ov) k x' τ' a ∧
      runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  rcases h.concrete.objectDeclRealized hdeclOld with ⟨a, hobjOld, hownOld, hliveOld⟩
  have hobjNew := runtimeFrameBindsObject_declareObjectState_forward_of_topFresh
    (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hobjOld
  have hownNew := runtimeFrameOwnsAddress_declareObjectState_forward
    (σ := σ) (τ := τ) (x := x) (ov := ov) hownOld
  have hane : a ≠ σ.next :=
    runtimeFrameOwnsAddress_ne_next_of_nextFresh
      (σ := σ) (k := k) (a := a) h.concrete.nextFresh hownOld
  have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
    (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
  exact ⟨a, hobjNew, hownNew, hliveNew⟩

theorem transport_old_ref_realization_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclRef Γ k x' τ') :
    ∃ a,
      runtimeFrameBindsRef (declareObjectState σ τ x ov) k x' τ' a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  rcases h.concrete.refDeclRealized hdeclOld with ⟨a, hrefOld, hliveOld⟩
  have hrefNew := runtimeFrameBindsRef_declareObjectState_forward_of_topFresh
    (σ := σ) (τ := τ) (x := x) (ov := ov) (h.topFrameFresh hΓ0) hrefOld
  have hane : a ≠ σ.next :=
    heapLiveTypedAt_ne_next_of_nextFresh
      (σ := σ) (a := a) (τ := τ') h.concrete.nextFresh hliveOld
  have hliveNew := heapLiveTypedAt_declareObjectState_of_ne
    (σ := σ) (τ := τ) (x := x) (ov := ov) (a := a) (υ := τ') hane hliveOld
  exact ⟨a, hrefNew, hliveNew⟩


theorem runtimeFrameOwnsAddress_declareObjectState_zero_next
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} :
    runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 σ.next := by
  unfold runtimeFrameOwnsAddress
  have hkσ0 : ∃ fr, (declareObjectState σ τ x ov).scopes[0]? = some fr := by
    cases hσ : σ.scopes <;>
      simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hσ]
  rcases hkσ0 with ⟨frσ0, hkσ0⟩
  refine ⟨frσ0, hkσ0, ?_⟩
  cases hσ : σ.scopes <;>
    simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hσ] at hkσ0 ⊢
  -- 1. frσ0 を具体的な構造体の内容で置き換える
  subst frσ0
  -- 2. リストの先頭に σ.next があることを証明する
  case nil =>
    simp
  case cons =>
    subst frσ0
    simp

theorem declare_new_object_realization_after_declareObjectState
    {σ : State} {x : Ident}
    {τ : CppType} {ov : Option Value} :
    ∃ a,
      runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ a ∧
      runtimeFrameOwnsAddress (declareObjectState σ τ x ov) 0 a ∧
      heapLiveTypedAt (declareObjectState σ τ x ov) a τ := by
  have hkσ0 : ∃ fr, (declareObjectState σ τ x ov).scopes[0]? = some fr := by
    cases hσ : σ.scopes <;>
      simp [declareObjectState, recordLocal, bindTopBinding, writeHeap, hσ]
  rcases hkσ0 with ⟨frσ0, hkσ0⟩
  have hobj : runtimeFrameBindsObject (declareObjectState σ τ x ov) 0 x τ σ.next :=
    runtimeFrameBindsObject_declareObjectState_zero_new
      (σ := σ) (τ := τ) (x := x) (ov := ov) hkσ0
  refine ⟨σ.next, hobj, ?_, ?_⟩
  · exact runtimeFrameOwnsAddress_declareObjectState_zero_next
      (σ := σ) (τ := τ) (x := x) (ov := ov)
  · simp

 theorem objectDeclRealized_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    ∀ {k x' τ'},
      typeFrameDeclObject (declareTypeObject Γ x τ) k x' τ' →
      ∃ a,
        runtimeFrameBindsObject (declareObjectState σ τ x ov) k x' τ' a ∧
        runtimeFrameOwnsAddress (declareObjectState σ τ x ov) k a ∧
        heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      rcases typeEnv_scopes_cons_of_zero_lookup (Γ := Γ) hΓ0 with ⟨fr0, frs, hsc⟩
      rcases hdecl with ⟨Γfr', hk, hb⟩
      rcases declareTypeObject_lookup_zero_frame_of_cons
        (Γ := Γ) (x := x) (τ := τ) (fr0 := fr0) (frs := frs) hsc hk with rfl
      by_cases hx' : x' = x
      · subst x'
        have : some (DeclInfo.object τ) = some (.object τ') := by simpa using hb
        cases this
        simpa using declare_new_object_realization_after_declareObjectState
          (σ := σ) (x := x) (τ := τ) (ov := ov)
      · have hdeclOld : typeFrameDeclObject Γ 0 x' τ' :=
          typeFrameDeclObject_declareTypeObject_zero_old_of_ne
            (Γ := Γ) (x := x) (x' := x') (τ := τ) (τ' := τ')
            (fr0 := fr0) (frs := frs) hsc hx' ⟨_, hk, hb⟩
        exact transport_old_object_realization_after_declareObjectState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclObject Γ k.succ x' τ' :=
        (typeFrameDeclObject_declareTypeObject_succ_iff
          (Γ := Γ) (x := x) (y := x') (τ := τ) (υ := τ') (k := k)).1 hdecl
      exact transport_old_object_realization_after_declareObjectState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld

 theorem refDeclRealized_after_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : DeclareObjectReadyStrong Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {ov : Option Value} :
    ∀ {k x' τ'},
      typeFrameDeclRef (declareTypeObject Γ x τ) k x' τ' →
      ∃ a,
        runtimeFrameBindsRef (declareObjectState σ τ x ov) k x' τ' a ∧
        heapLiveTypedAt (declareObjectState σ τ x ov) a τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      rcases typeEnv_scopes_cons_of_zero_lookup (Γ := Γ) hΓ0 with ⟨fr0, frs, hsc⟩
      have hdeclOld : typeFrameDeclRef Γ 0 x' τ' :=
        typeFrameDeclRef_declareTypeObject_zero_old
          (Γ := Γ) (x := x) (x' := x') (τ := τ) (τ' := τ')
          (fr0 := fr0) (frs := frs) hsc hdecl
      exact transport_old_ref_realization_after_declareObjectState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclRef Γ k.succ x' τ' :=
        (typeFrameDeclRef_declareTypeObject_succ_iff
          (Γ := Γ) (x := x) (y := x') (τ := τ) (υ := τ') (k := k)).1 hdecl
      exact transport_old_ref_realization_after_declareObjectState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (ov := ov) hdeclOld

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

theorem transport_old_object_realization_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclObject Γ k x' τ') :
    ∃ addr,
      runtimeFrameBindsObject (declareRefState σ τ x a) k x' τ' addr ∧
      runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr ∧
      heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  rcases h.concrete.objectDeclRealized hdeclOld with ⟨addr, hobjOld, hownOld, hliveOld⟩
  have hobjNew := runtimeFrameBindsObject_declareRefState_forward_of_topFresh
    (σ := σ) (τ := τ) (x := x) (a := a) (h.topFrameFresh hΓ0) hobjOld
  have hownNew := (runtimeFrameOwnsAddress_declareRefState_iff
    (σ := σ) (τ := τ) (x := x) (a := a) (k := k) (addr := addr)).2 hownOld
  have hliveNew := (heapLiveTypedAt_declareRefState_iff
    (σ := σ) (τ := τ) (x := x) (r := a) (a := addr) (υ := τ')).2 hliveOld
  exact ⟨addr, hobjNew, hownNew, hliveNew⟩

theorem transport_old_ref_realization_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    {k : Nat} {x' : Ident} {τ' : CppType}
    (hdeclOld : typeFrameDeclRef Γ k x' τ') :
    ∃ addr,
      runtimeFrameBindsRef (declareRefState σ τ x a) k x' τ' addr ∧
      heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  rcases h.concrete.refDeclRealized hdeclOld with ⟨addr, hrefOld, hliveOld⟩
  have hrefNew := runtimeFrameBindsRef_declareRefState_forward_of_topFresh
    (σ := σ) (τ := τ) (x := x) (a := a) (h.topFrameFresh hΓ0) hrefOld
  have hliveNew := (heapLiveTypedAt_declareRefState_iff
    (σ := σ) (τ := τ) (x := x) (r := a) (a := addr) (υ := τ')).2 hliveOld
  exact ⟨addr, hrefNew, hliveNew⟩

 theorem objectDeclRealized_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat} :
    ∀ {k x' τ'},
      typeFrameDeclObject (declareTypeRef Γ x τ) k x' τ' →
      ∃ addr,
        runtimeFrameBindsObject (declareRefState σ τ x a) k x' τ' addr ∧
        runtimeFrameOwnsAddress (declareRefState σ τ x a) k addr ∧
        heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      rcases typeEnv_scopes_cons_of_zero_lookup (Γ := Γ) hΓ0 with ⟨fr0, frs, hsc⟩
      have hdeclOld : typeFrameDeclObject Γ 0 x' τ' :=
        typeFrameDeclObject_declareTypeRef_zero_old
          (Γ := Γ) (x := x) (x' := x') (τ := τ) (τ' := τ')
          (fr0 := fr0) (frs := frs) hsc hdecl
      exact transport_old_object_realization_after_declareRefState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclObject Γ k.succ x' τ' :=
        (typeFrameDeclObject_declareTypeRef_succ_iff
          (Γ := Γ) (x := x) (y := x') (τ := τ) (υ := τ') (k := k)).1 hdecl
      exact transport_old_object_realization_after_declareRefState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld


theorem declare_new_ref_realization_after_declareRefState
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (haLive : heapLiveTypedAt σ a τ) :
    ∃ addr,
      runtimeFrameBindsRef (declareRefState σ τ x a) 0 x τ addr ∧
      heapLiveTypedAt (declareRefState σ τ x a) addr τ := by
  have hkσ0 : ∃ fr, (declareRefState σ τ x a).scopes[0]? = some fr := by
    cases hσ : σ.scopes with
    | nil =>
        simp [declareRefState, bindTopBinding, hσ]
    | cons fr frs =>
        simp [declareRefState, bindTopBinding, hσ]
  rcases hkσ0 with ⟨_, hkσ0⟩
  refine ⟨a, ?_, ?_⟩
  · exact runtimeFrameBindsRef_declareRefState_zero_new
      (σ := σ) (τ := τ) (x := x) (a := a) hkσ0
  · exact
      (heapLiveTypedAt_declareRefState_iff
        (σ := σ) (τ := τ) (x := x) (r := a) (a := a) (υ := τ)).2 haLive

 theorem refDeclRealized_after_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident}
    (h : Ready Γ σ x)
    {Γfr : TypeFrame}
    (hΓ0 : Γ.scopes[0]? = some Γfr)
    {τ : CppType} {a : Nat}
    (haLive : heapLiveTypedAt σ a τ) :
    ∀ {k x' τ'},
      typeFrameDeclRef (declareTypeRef Γ x τ) k x' τ' →
      ∃ addr,
        runtimeFrameBindsRef (declareRefState σ τ x a) k x' τ' addr ∧
        heapLiveTypedAt (declareRefState σ τ x a) addr τ' := by
  intro k x' τ' hdecl
  cases k with
  | zero =>
      rcases typeEnv_scopes_cons_of_zero_lookup (Γ := Γ) hΓ0 with ⟨fr0, frs, hsc⟩
      rcases hdecl with ⟨Γfr', hk, hb⟩
      rcases declareTypeRef_lookup_zero_frame_of_cons
        (Γ := Γ) (x := x) (τ := τ) (fr0 := fr0) (frs := frs) hsc hk with rfl
      by_cases hx' : x' = x
      · subst x'
        have : some (DeclInfo.ref τ) = some (.ref τ') := by simpa using hb
        cases this
        exact declare_new_ref_realization_after_declareRefState
          (σ := σ) (τ := τ) (x := x) (a := a) haLive
      · have hdeclOld : typeFrameDeclRef Γ 0 x' τ' :=
        typeFrameDeclRef_declareTypeRef_zero_old_of_ne
            (Γ := Γ) (x := x) (x' := x') (τ := τ) (τ' := τ')
            (fr0 := fr0) (frs := frs) hsc hx' ⟨_, hk, hb⟩
        exact transport_old_ref_realization_after_declareRefState
          (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld
  | succ k =>
      have hdeclOld : typeFrameDeclRef Γ k.succ x' τ' :=
        (typeFrameDeclRef_declareTypeRef_succ_iff
          (Γ := Γ) (x := x) (y := x') (τ := τ) (υ := τ') (k := k)).1 hdecl
      exact transport_old_ref_realization_after_declareRefState
        (h := h) (hΓ0 := hΓ0) (τ := τ) (a := a) hdeclOld

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
