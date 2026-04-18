import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectRealizers
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectOwnership
import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectTransport
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteStrengthening
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCore

namespace Cpp

/-!
# Closure.Transitions.Major.DeclareObjectDecomposition

`declareObject` の final assembly 層。

このファイルでは、
- frame-depth / heap-stored-values / fresh-next といった構造 field
- binding soundness
- `ScopedTypedStateConcrete` への最終組み立て

だけを扱う。type-side 分解、realizer 回収、ownership transport は
それぞれ専用ファイルへ分離した。
-/

/-! =========================================================
    1. 構造 field の preservation
    ========================================================= -/

theorem declareObject_preserves_frameDepthAgreement
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    frameDepthAgreement (declareTypeObject Γ x τ) σ' := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hΓ : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hΓ] at hfresh
  | cons Γfr Γrs =>
      cases hσs : σ.scopes with
      | nil =>
          simp [currentScopeFresh, hσs] at hsfresh
      | cons σfr σrs =>
          simpa [frameDepthAgreement, declareTypeObject, insertTopDecl, hΓ,
            declareObjectStateWithNext, setNext, declareObjectStateCore,
            recordLocal, writeHeap, bindTopBinding, hσs] using hσ.frameDepth

private theorem lookupDecl_declareTypeObject_self
    (Γ : TypeEnv) (x : Ident) (τ : CppType) :
    lookupDecl (declareTypeObject Γ x τ) x = some (.object τ) := by
  unfold lookupDecl
  cases hsc : Γ.scopes <;>
    simp [lookupDeclFrames, declareTypeObject, insertTopDecl, hsc]

private theorem lookupDecl_declareTypeObject_other
    (Γ : TypeEnv) (x y : Ident) (τ : CppType)
    (hy : y ≠ x) :
    lookupDecl (declareTypeObject Γ x τ) y = lookupDecl Γ y := by
  unfold lookupDecl
  cases hsc : Γ.scopes <;>
    simp [lookupDeclFrames, declareTypeObject, insertTopDecl, hsc, hy]

theorem declareObject_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    shadowingCompatible (declareTypeObject Γ x τ) σ' := by
  intro hσ hfresh hdecl y d hlookup
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  by_cases hy : y = x
  ·
    subst hy
    rw [lookupDecl_declareTypeObject_self] at hlookup
    injection hlookup with hd; subst hd

    exists Binding.object τ σ.next
    constructor
    · simp [setNext, declareObjectStateCore, bindTopBinding, lookupBinding]
      cases hsc : σ.scopes <;> simp [lookupBindingFrames]
    · simp [DeclMatchesBinding]

  ·
    rw [lookupDecl_declareTypeObject_other _ _ _ _ hy] at hlookup

    have hlookup_bound : lookupBinding (setNext (declareObjectStateCore σ τ x ov) aNext) y = lookupBinding σ y := by
      simp [setNext, declareObjectStateCore, bindTopBinding, lookupBinding]
      cases hsc : σ.scopes <;> simp [lookupBindingFrames,  hy]

    rw [hlookup_bound]
    exact hσ.shadowing y d hlookup

private theorem frameDeclBindingExactAt_insertTop
    {Γfr : TypeFrame} {σfr : ScopeFrame}
    {x : Ident} {d : DeclInfo} {b : Binding} :
    frameDeclBindingExactAt Γfr σfr →
    Γfr.decls x = none →
    σfr.binds x = none →
    DeclMatchesBinding d b →
    frameDeclBindingExactAt
      { Γfr with decls := fun y => if y = x then some d else Γfr.decls y }
      { σfr with binds := fun y => if y = x then some b else σfr.binds y } := by
  intro hexact hdeclFresh hbindFresh hmatch
  constructor
  · intro y d' hdecl
    by_cases hy : y = x
    · subst hy
      have hd' : d' = d := by
        simpa [hdeclFresh] using hdecl.symm
      subst hd'
      exact ⟨b, by simp, hmatch⟩
    · have hdeclOld : Γfr.decls y = some d' := by
        simpa [hy] using hdecl
      rcases frameDeclBindingExactAt_forward hexact hdeclOld with ⟨b', hb', hmatch'⟩
      exact ⟨b', by simpa [hy] using hb', hmatch'⟩
  · intro y b' hbind
    by_cases hy : y = x
    · subst hy
      have hb' : b' = b := by
        simpa [hbindFresh] using hbind.symm
      subst hb'
      exact ⟨d, by simp , hmatch⟩
    · have hbindOld : σfr.binds y = some b' := by
        simpa [hy] using hbind
      rcases frameDeclBindingExactAt_backward hexact hbindOld with ⟨d', hdecl', hmatch'⟩
      exact ⟨d', by simpa [hy] using hdecl', hmatch'⟩

theorem declareObject_preserves_framewiseDeclBindingExact
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    framewiseDeclBindingExact (declareTypeObject Γ x τ) σ' := by
  intro hσ hfresh hdecl
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
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
              -- 1. 現時点のフレーム整合性と、型環境が Fresh である事実を取り出す
              have hExact0 : frameDeclBindingExactAt Γtop σtop :=
                hσ.namesExact 0 Γtop σtop (by simp [hΓ]) (by simp [hS])
              have hTypeFresh0 : Γtop.decls x = none := by
                simpa [currentTypeScopeFresh, hΓ] using hfresh

              -- 2. 【補題のインライン化】σtop.binds x = none であることを直接証明
              have hRunFresh0 : σtop.binds x = none := by
                match hbx : σtop.binds x with
                | none => rfl
                | some b =>
                    -- もし binding が存在したなら、hExact0 の backward 側を使って矛盾を導く
                    let h_backward := hExact0.right
                    match h_backward x b hbx with
                    | ⟨d, h_decl_at_x, _hmatch⟩ =>
                        -- Γtop.decls x が none かつ some d なので矛盾
                        rw [hTypeFresh0] at h_decl_at_x
                        contradiction

              -- 3. 新しいフレームでの整合性 (frameDeclBindingExactAt) を構築
              have hTop :
                  frameDeclBindingExactAt
                    { Γtop with decls := fun y => if y = x then some (.object τ) else Γtop.decls y }
                    { σtop with
                      binds := fun y => if y = x then some (.object τ σ.next) else σtop.binds y,
                      locals := σ.next :: σtop.locals } :=
                frameDeclBindingExactAt_insertTop
                  hExact0 hTypeFresh0 hRunFresh0 (by simp [DeclMatchesBinding])

              -- 4. ゴールの Γfr, σfr を具体化して hTop を適用
              have hΓfr : Γfr = { Γtop with decls := fun y => if y = x then some (.object τ) else Γtop.decls y } := by
                simpa [declareTypeObject, insertTopDecl, hΓ] using hkΓ.symm

              have hσfr : σfr = { σtop with
                  binds := fun y => if y = x then some (.object τ σ.next) else σtop.binds y,
                  locals := σ.next :: σtop.locals } := by
                -- setNext aNext は σ.next の更新を反映
                simpa [setNext, declareObjectStateCore, recordLocal, writeHeap, bindTopBinding, hS] using hkσ.symm

              rw [hΓfr, hσfr]
              exact hTop
          | succ j =>
              have hkΓOld : Γ.scopes[(j + 1)]? = some Γfr := by
                simpa [declareTypeObject, insertTopDecl, hΓ] using hkΓ
              have hkσOld : σ.scopes[(j + 1)]? = some σfr := by
                simpa [scopes_declareObjectStateWithNext_eq_old, declareObjectState,
                  recordLocal, bindTopBinding, writeHeap, hS] using hkσ
              exact hσ.namesExact (j + 1) Γfr σfr hkΓOld hkσOld

/-! =========================================================
    2. binding soundness
    ========================================================= -/

theorem declareObject_preserves_objectBindingSound
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    objectBindingSound σ' := by
  intro hσ hfresh hdecl
  intro k y υ a hbind
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          rcases DeclareObjectTransport.runtimeFrameBindsObject_zero_declareObjectStateWithNext_cases
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (y := y) (υ := υ) (a := a) hsc hbind with
            hnew | hbindOld
          · rcases hnew with ⟨hy, hυ, ha⟩
            subst hy
            subst hυ
            subst ha
            refine ⟨?_, ?_⟩
            ·
              apply DeclareObjectTransport.runtimeFrameOwnsAddress_zero_new_declareObjectStateWithNext (σ := σ) (τ := υ) (x := y) (ov := ov) (aNext := aNext) (fr := fr) (frs := frs)
              · exact hsc
            ·
              refine ⟨{ ty := υ, value := ov, alive := true }, ?_, rfl, rfl⟩
              let a := σ.next
              simp [setNext, declareObjectStateCore, recordLocal, writeHeap, hsc]

          · rcases hσ.objectBindingSound hbindOld with ⟨hownOld, hliveOld⟩
            have ha : a ≠ σ.next := by
              intro hEq
              subst hEq
              rcases hliveOld with ⟨c, hheap, htyc, halive⟩
              rw [hheapNone] at hheap
              simp at hheap
            refine ⟨?_, ?_⟩
            · exact
                DeclareObjectTransport.runtimeFrameOwnsAddress_zero_preserved_declareObjectStateWithNext
                  (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                  (fr := fr) (frs := frs) (a := a) hsc hownOld
            · exact
                DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                  (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                  (a := a) (υ := υ) ha hliveOld
      | succ j =>
          have hbindOld :
              runtimeFrameBindsObject σ (j + 1) y υ a :=
            DeclareObjectTransport.runtimeFrameBindsObject_succ_declareObjectStateWithNext_inv
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (j := j) (y := y) (υ := υ) (a := a) hsc hbind
          rcases hσ.objectBindingSound hbindOld with ⟨hownOld, hliveOld⟩
          have ha : a ≠ σ.next := by
            intro hEq
            subst hEq
            rcases hliveOld with ⟨c, hheap, htyc, halive⟩
            rw [hheapNone] at hheap
            simp at hheap
          refine ⟨?_, ?_⟩
          · exact
              DeclareObjectTransport.runtimeFrameOwnsAddress_succ_preserved_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (fr := fr) (frs := frs) (j := j) (a := a) hsc hownOld
          · exact
              DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (a := a) (υ := υ) ha hliveOld

theorem declareObject_preserves_refBindingSound
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    refBindingSound σ' := by
  intro hσ hfresh hdecl
  intro k y υ a hbind
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          rcases hbind with ⟨fr', hk, hb⟩
          let frNew : ScopeFrame :=
            { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z
              locals := σ.next :: fr.locals }
          have hfr' : fr' = frNew := by
            simpa [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
              recordLocal, writeHeap, bindTopBinding, hsc] using hk.symm
          subst fr'
          have hy : y ≠ x := by
            intro hEq
            subst y
            simp [frNew] at hb
          have hbindOld : runtimeFrameBindsRef σ 0 y υ a := by
            refine ⟨fr, by simp [hsc], ?_⟩
            simpa [frNew, hy] using hb
          have hliveOld : heapLiveTypedAt σ a υ := hσ.refBindingSound hbindOld
          have ha : a ≠ σ.next := by
            intro hEq
            subst hEq
            rcases hliveOld with ⟨c, hheap, htyc, halive⟩
            rw [hheapNone] at hheap
            simp at hheap
          exact
            DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (a := a) (υ := υ) ha hliveOld
      | succ j =>
          have hbindOld :
              runtimeFrameBindsRef σ (j + 1) y υ a :=
            DeclareObjectTransport.runtimeFrameBindsRef_succ_declareObjectStateWithNext_inv
              (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) (aNext := aNext)
              (υ := υ) (j := j) (a := a) (fr := fr) (frs := frs) hsc hbind
          have hliveOld : heapLiveTypedAt σ a υ := hσ.refBindingSound hbindOld
          have ha : a ≠ σ.next := by
            intro hEq
            subst hEq
            rcases hliveOld with ⟨c, hheap, htyc, halive⟩
            rw [hheapNone] at hheap
            simp at hheap
          exact
            DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (a := a) (υ := υ) ha hliveOld

theorem declareObject_preserves_nextFreshAgainstOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    nextFreshAgainstOwned σ' := by
  intro _ _ hdecl
  rcases hdecl with ⟨aNext, hdeclNext⟩
  rcases declaresObjectWithNext_postCursorFresh hdeclNext with ⟨hheapNone, hlocals⟩
  exact ⟨hheapNone, hlocals⟩

theorem declareObject_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a j},
      runtimeFrameBindsRef σ' k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a := by
  intro hσ hfresh hdecl k y υ a j hbind hjk
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          cases Nat.not_lt_zero _ hjk
      | succ k' =>
          have hbindOld :
              runtimeFrameBindsRef σ (k' + 1) y υ a :=
            DeclareObjectTransport.runtimeFrameBindsRef_succ_declareObjectStateWithNext_inv
              (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) (aNext := aNext)
              (υ := υ) (j := k') (a := a) (fr := fr) (frs := frs) hsc hbind
          have hliveOld : heapLiveTypedAt σ a υ := hσ.refBindingSound hbindOld
          have ha : a ≠ σ.next := by
            intro hEq
            subst hEq
            rcases hliveOld with ⟨c, hheap, htyc, halive⟩
            rw [hheapNone] at hheap
            simp at hheap
          cases j with
          | zero =>
              intro hown
              rcases DeclareObjectTransport.runtimeFrameOwnsAddress_zero_declareObjectStateWithNext_cases
                  (σ := σ) (aNext := aNext) (x := x) (τ := τ) (ov := ov)
                  (fr := fr) (frs := frs) hsc hown with hnew | hownOld
              · subst hnew
                exact ha rfl
              · exact hσ.refTargetsAvoidInnerOwned hbindOld (Nat.zero_lt_succ k') hownOld
          | succ j' =>
              intro hown
              have hownOld :
                  runtimeFrameOwnsAddress σ (j' + 1) a :=
                DeclareObjectTransport.runtimeFrameOwnsAddress_succ_declareObjectStateWithNext_inv
                  (σ := σ) (aNext := aNext) (x := x) (τ := τ) (ov := ov)
                  (fr := fr) (frs := frs) (j := j') (a := a) hsc hown
              exact hσ.refTargetsAvoidInnerOwned hbindOld hjk hownOld

/-- オブジェクト宣言はヒープ全体の型整合性を保存する。 -/
theorem declareObject_preserves_heapInitializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    heapInitializedValuesTyped σ' := by
  intro hσ _ hdecl
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobj, hfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hstate⟩
  subst σcore
  subst hstate
  intro a c v hheap hval
  by_cases ha : a = σ.next
  · subst ha
    simp [setNext] at hheap
    subst hheap
    simp at hval
    simp
    rw [hval] at hovcompat
    exact hovcompat
  · have h_other : (setNext (declareObjectStateCore σ τ x ov) aNext).heap a = σ.heap a := by
      simp [setNext]
      cases σ.scopes <;> simp [ha]
    rw [h_other] at hheap
    exact hσ.heapStoredValuesTyped a c v hheap hval

/-! =========================================================
    3. 最終組み立て
    ========================================================= -/

theorem declareObject_concrete_state_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ' := by
  intro hfresh hσ hdecl
  refine
    { frameDepth := ?_
      namesExact := ?_
      shadowing := ?_
      objectDeclRealized := ?_
      refDeclRealized := ?_
      objectBindingSound := ?_
      refBindingSound := ?_
      ownedAddressNamed := ?_
      refsNotOwned := ?_
      objectsOwned := ?_
      ownedNoDupPerFrame := ?_
      ownedDisjoint := ?_
      ownedNamed := ?_
      heapStoredValuesTyped := ?_
      nextFresh := ?_
      refTargetsAvoidInnerOwned := ?_ }

  · exact declareObject_preserves_frameDepthAgreement hσ hfresh hdecl
  · exact declareObject_preserves_framewiseDeclBindingExact hσ hfresh hdecl
  · exact declareObject_preserves_shadowingCompatible hσ hfresh hdecl
  · intro k y υ hty
    exact declareObject_objectDeclRealized_of_decomposition hfresh hσ hdecl hty
  · intro k y υ hty
    exact declareObject_refDeclRealized_of_decomposition hfresh hσ hdecl hty
  · exact declareObject_preserves_objectBindingSound hσ hfresh hdecl
  · exact declareObject_preserves_refBindingSound hσ hfresh hdecl
  · intro k a hown
    exact declareObject_preserves_ownedAddressNamed hσ hfresh hdecl hown
  · exact declareObject_preserves_refBindingsNeverOwned hσ hfresh hdecl
  · exact declareObject_preserves_allObjectBindingsOwned hσ hfresh hdecl
  · exact declareObject_preserves_ownedNoDupPerFrame hσ hfresh hdecl
  · exact declareObject_preserves_ownedDisjointAcrossFrames hσ hfresh hdecl
  · exact declareObject_preserves_allOwnedAddressesNamed hσ hfresh hdecl
  · exact declareObject_preserves_heapInitializedValuesTyped hσ hfresh hdecl
  · exact declareObject_preserves_nextFreshAgainstOwned hσ hfresh hdecl
  · intro k y υ a j hbind hjk
    exact declareObject_preserves_refTargetsAvoidInnerOwned hσ hfresh hdecl hbind hjk

theorem declares_object_preserves_scoped_typed_state_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ScopedTypedStateConcrete (declareTypeObject Γ x τ) σ' := by
  intro hfresh hσ hdecl
  exact declareObject_concrete_state_of_decomposition hfresh hσ hdecl

end Cpp
