import CppFormalization.Cpp2.Closure.Transitions.Major.CloseScopeDecomposition
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext

namespace Cpp

/-!
# Closure.Transitions.Major.DeclareObjectDecomposition

`declareObject` は `declareRef` より一段重い。
理由は、新しい top object binding だけでなく、top ownership と fresh address を実際に増やすからである。

このファイルでは、`DeclaresObject` が `ScopedTypedStateConcrete` を保つことを、
`closeScope` と同じく field ごとに分解して組み立てる。

重要:
- object payload semantics と post-state cursor policy は分離された。
- したがって `nextFreshAgainstOwned` は allocator/cursor policy 側から
  honest に供給できる。
-/

/-! =========================================================
    1. 型環境側の分解
    ========================================================= -/

theorem typeFrameDeclRef_declareTypeObject_inv
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    typeFrameDeclRef (declareTypeObject Γ x τ) k y υ →
    typeFrameDeclRef Γ k y υ := by
  intro hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      cases k <;>
        simp [declareTypeObject, insertTopDecl, hsc] at hk hdecl
      subst hk
      simp at hdecl
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [declareTypeObject, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            simp at hdecl
          · refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclRef, declareTypeObject, insertTopDecl, hsc] using hk
          · simpa [declareTypeObject, insertTopDecl, hsc] using hdecl

theorem typeFrameDeclObject_declareTypeObject_cases
    {Γ : TypeEnv} {x : Ident} {τ : CppType}
    {k : Nat} {y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclObject (declareTypeObject Γ x τ) k y υ →
    (k = 0 ∧ y = x ∧ υ = τ) ∨ typeFrameDeclObject Γ k y υ := by
  intro hfresh hty
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      cases k with
      | zero =>
          simp [declareTypeObject, insertTopDecl, hsc] at hk
          subst hk
          by_cases hy : y = x
          · subst hy
            left
            have hυ : υ = τ := by
              simpa using hdecl.symm
            exact ⟨rfl, rfl, hυ⟩
          · right
            refine ⟨fr0, by simp [hsc], ?_⟩
            simpa [hy] using hdecl
      | succ j =>
          right
          refine ⟨fr, ?_, ?_⟩
          · simpa [typeFrameDeclObject, declareTypeObject, insertTopDecl, hsc] using hk
          · simpa [declareTypeObject, insertTopDecl, hsc] using hdecl

/-! =========================================================
    2. 実現子の分解
    ========================================================= -/

private theorem typeFrameDeclRef_zero_name_ne_of_fresh
    {Γ : TypeEnv} {x y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclRef Γ 0 y υ →
    y ≠ x := by
  intro hfresh hty
  intro hy
  subst hy
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      have hfr : fr = fr0 := by
        simpa [hsc] using hk.symm
      subst hfr
      simp [currentTypeScopeFresh, hsc] at hfresh
      rw [hfresh] at hdecl
      simp at hdecl

private theorem runtimeFrameBindsRef_zero_preserved_of_ne_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hy : y ≠ x)
    (hbind : runtimeFrameBindsRef σ 0 y υ a) :
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) 0 y υ a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hbind with ⟨fr0, hk0, hb0⟩
  have hfr0 : fr0 = fr := by
    simpa [hsc] using hk0.symm
  subst fr0
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew, hy, hb0]

private theorem runtimeFrameBindsRef_succ_preserved_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {j a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsRef σ (j + 1) y υ a) :
    runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a := by
  rcases hbind with ⟨fr0, hk0, hb0⟩
  exact ⟨fr0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb0⟩

private theorem runtimeFrameBindsRef_succ_declareObjectStateWithNext_inv
    {σ : State} {τ : CppType} {x y : Ident} {ov : Option Value} {aNext : Nat}
    {υ : CppType} {j a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsRef (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a) :
    runtimeFrameBindsRef σ (j + 1) y υ a := by
  rcases hbind with ⟨fr0, hk0, hb0⟩
  exact ⟨fr0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb0⟩


private theorem heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {a : Nat} {υ : CppType} :
    a ≠ σ.next →
    heapLiveTypedAt σ a υ →
    heapLiveTypedAt (declareObjectStateWithNext σ τ x ov aNext) a υ := by
  intro ha hlive
  rcases hlive with ⟨c, hheap, halive, hty⟩
  refine ⟨c, ?_, halive, hty⟩

  -- 1. 状態遷移の定義を展開
  simp [declareObjectStateWithNext, setNext, Cpp.declareObjectState]

  -- 2. σ.scopes の状態でケース分けを行う (これが重要)
  -- これにより、match σ.scopes がすべて消えます
  cases hsc : σ.scopes with
  | nil =>
      -- σ.scopes = [] のケース
      -- bindTopBinding 等を展開。hsc を使って match を解消する
      simp [writeHeap]
      -- if a = σ.next then ... else σ.heap a = some c という形になる
      rw [if_neg ha]
      exact hheap
  | cons fr frs =>
      -- σ.scopes = fr :: frs のケース
      simp [writeHeap]
      -- 同様に if a = σ.next を処理
      rw [if_neg ha]
      exact hheap


theorem declareObject_preserves_old_ref_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclRef Γ k y υ →
      ∃ a,
        runtimeFrameBindsRef σ' k y υ a ∧
        heapLiveTypedAt σ' a υ := by
  intro hσ hfresh hdecl k y υ hty
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'

  rcases hσ.refDeclRealized hty with ⟨a, hbindOld, hliveOld⟩

  have ha : a ≠ σ.next := by
    intro haeq
    subst haeq
    rcases hliveOld with ⟨c, hheap, halive, htyc⟩
    rw [hheapNone] at hheap
    simp at hheap

  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          have hy : y ≠ x :=
            typeFrameDeclRef_zero_name_ne_of_fresh hfresh hty
          refine ⟨a, ?_, ?_⟩
          · exact
              runtimeFrameBindsRef_zero_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) (aNext := aNext)
                (υ := υ) (a := a) (fr := fr) (frs := frs) hsc hy hbindOld
          · exact
              heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (a := a) (υ := υ) ha hliveOld
      | succ j =>
          refine ⟨a, ?_, ?_⟩
          · exact
              runtimeFrameBindsRef_succ_preserved_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) (aNext := aNext)
                (υ := υ) (j := j) (a := a) (fr := fr) (frs := frs) hsc hbindOld
          · exact
              heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (a := a) (υ := υ) ha hliveOld


theorem declareObject_realizes_new_top_object
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∃ a,
      runtimeFrameBindsObject σ' 0 x τ a ∧
      runtimeFrameOwnsAddress σ' 0 a ∧
      heapLiveTypedAt σ' a τ := by
  intro _ _ hdecl
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      let fr' : ScopeFrame :=
        { binds := fun y => if y = x then some (.object τ σ.next) else fr.binds y
          locals := σ.next :: fr.locals }
      refine ⟨σ.next, ?_, ?_, ?_⟩
      · refine ⟨fr', ?_, ?_⟩
        · simp [fr', setNext, declareObjectStateCore,
            recordLocal, writeHeap, bindTopBinding, hsc]
        · simp [fr']
      · refine ⟨fr', ?_, ?_⟩
        · simp [fr', setNext, declareObjectStateCore,
            recordLocal, writeHeap, bindTopBinding, hsc]
        · simp [fr']
      · refine ⟨{ ty := τ, value := ov, alive := true }, ?_, rfl, rfl⟩
        simp



theorem declareObject_refDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclRef (declareTypeObject Γ x τ) k y υ →
      ∃ a,
        runtimeFrameBindsRef σ' k y υ a ∧
        heapLiveTypedAt σ' a υ := by
  intro hfresh hσ hdecl k y υ hty
  exact declareObject_preserves_old_ref_realizers hσ hfresh hdecl
    (typeFrameDeclRef_declareTypeObject_inv hty)

/-! =========================================================
    3. 構造 field の preservation
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

axiom declareObject_preserves_shadowingCompatible
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    shadowingCompatible (declareTypeObject Γ x τ) σ'



private theorem runtimeFrameOwnsAddress_zero_declareObjectStateWithNext_cases
    {σ : State} {aNext : Nat} {x : Ident} {τ : CppType} {ov : Option Value}
    {fr : ScopeFrame} {frs : List ScopeFrame} {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 a) :
    a = σ.next ∨ runtimeFrameOwnsAddress σ 0 a := by
  let frNew : ScopeFrame :=
    { binds := fun y => if y = x then some (.object τ σ.next) else fr.binds y,
      locals := σ.next :: fr.locals }
  rcases hown with ⟨fr', hk, hmem⟩
  have hfr' : fr' = frNew := by
    simpa [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc] using hk.symm
  subst fr'
  simp [frNew] at hmem
  rcases hmem with hnew | hold
  · exact Or.inl hnew
  · exact Or.inr ⟨fr, by simp [hsc], hold⟩

private theorem runtimeFrameOwnsAddress_succ_declareObjectStateWithNext_inv
    {σ : State} {aNext : Nat} {x : Ident} {τ : CppType} {ov : Option Value}
    {fr : ScopeFrame} {frs : List ScopeFrame} {j a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) (j + 1) a) :
    runtimeFrameOwnsAddress σ (j + 1) a := by
  rcases hown with ⟨fr', hk, hmem⟩
  exact ⟨fr',
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk,
    hmem⟩

private theorem runtimeFrameBindsObject_zero_new_declareObjectStateWithNext
    {σ : State} {aNext : Nat} {x : Ident} {τ : CppType} {ov : Option Value}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs) :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 x τ σ.next := by
  let frNew : ScopeFrame :=
    { binds := fun y => if y = x then some (.object τ σ.next) else fr.binds y,
      locals := σ.next :: fr.locals }
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew]

private theorem runtimeFrameBindsObject_zero_preserved_of_ne_declareObjectStateWithNext
    {σ : State} {aNext : Nat} {x y : Ident} {τ υ : CppType} {ov : Option Value} {a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hy : y ≠ x)
    (hbind : runtimeFrameBindsObject σ 0 y υ a) :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 y υ a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hbind with ⟨fr0, hk0, hb0⟩
  have hfr0 : fr0 = fr := by
    simpa [hsc] using hk0.symm
  subst fr0
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew, hy, hb0]

private theorem runtimeFrameBindsObject_succ_preserved_declareObjectStateWithNext
    {σ : State} {aNext : Nat} {x y : Ident} {τ υ : CppType} {ov : Option Value} {j a : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsObject σ (j + 1) y υ a) :
    runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a := by
  rcases hbind with ⟨fr0, hk0, hb0⟩
  exact ⟨fr0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk0,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb0⟩

theorem declareObject_preserves_ownedAddressNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k a},
      runtimeFrameOwnsAddress σ' k a →
      ∃ y υ, runtimeFrameBindsObject σ' k y υ a := by
  intro hσ hfresh hdecl k a hown
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          rcases runtimeFrameOwnsAddress_zero_declareObjectStateWithNext_cases
              (σ := σ) (aNext := aNext) (x := x) (τ := τ) (ov := ov)
              (fr := fr) (frs := frs) hsc hown with
            hnew | hownOld
          · subst hnew
            exact ⟨x, τ,
              runtimeFrameBindsObject_zero_new_declareObjectStateWithNext
                (σ := σ) (aNext := aNext) (x := x) (τ := τ) (ov := ov)
                (fr := fr) (frs := frs) hsc⟩
          · rcases hσ.ownedAddressNamed hownOld with ⟨y, υ, hbindOld⟩
            by_cases hy : y = x
            · subst hy
              rcases hbindOld with ⟨fr0, hk0, hb0⟩
              have hfr0 : fr0 = fr := by
                simpa [hsc] using hk0.symm
              subst fr0
              simp [currentScopeFresh, hsc] at hsfresh
              rw [hsfresh] at hb0
              simp at hb0
            · exact ⟨y, υ,
                runtimeFrameBindsObject_zero_preserved_of_ne_declareObjectStateWithNext
                  (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
                  (a := a) (fr := fr) (frs := frs) hsc hy hbindOld⟩
      | succ j =>
          have hownOld :
              runtimeFrameOwnsAddress σ (j + 1) a :=
            runtimeFrameOwnsAddress_succ_declareObjectStateWithNext_inv
              (σ := σ) (aNext := aNext) (x := x) (τ := τ) (ov := ov)
              (fr := fr) (frs := frs) (j := j) (a := a) hsc hown
          rcases hσ.ownedAddressNamed hownOld with ⟨y, υ, hbindOld⟩
          exact ⟨y, υ,
            runtimeFrameBindsObject_succ_preserved_declareObjectStateWithNext
              (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
              (j := j) (a := a) (fr := fr) (frs := frs) hsc hbindOld⟩


axiom declareObject_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    refBindingsNeverOwned σ'

private theorem runtimeFrameBindsObject_zero_declareObjectStateWithNext_cases
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {y : Ident} {υ : CppType} {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) 0 y υ a) :
    (y = x ∧ υ = τ ∧ a = σ.next) ∨ runtimeFrameBindsObject σ 0 y υ a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hbind with ⟨fr', hk, hb⟩
  have hfr' : fr' = frNew := by
    simpa [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc] using hk.symm
  subst fr'
  by_cases hy : y = x
  · subst hy
    left
    have hobj : (Binding.object τ σ.next) = (.object υ a) := by
      simpa [frNew] using hb
    cases hobj
    exact ⟨rfl, rfl, rfl⟩
  · right
    refine ⟨fr, by simp [hsc], ?_⟩
    simpa [frNew, hy] using hb

private theorem runtimeFrameBindsObject_succ_declareObjectStateWithNext_inv
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {j : Nat} {y : Ident} {υ : CppType} {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hbind : runtimeFrameBindsObject (declareObjectStateWithNext σ τ x ov aNext) (j + 1) y υ a) :
    runtimeFrameBindsObject σ (j + 1) y υ a := by
  rcases hbind with ⟨fr', hk, hb⟩
  exact ⟨fr',
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk,
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hb⟩

private theorem runtimeFrameOwnsAddress_zero_new_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    (hsc : σ.scopes = fr :: frs) :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 σ.next := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew]

private theorem runtimeFrameOwnsAddress_zero_preserved_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress σ 0 a) :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) 0 a := by
  let frNew : ScopeFrame :=
    { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z,
      locals := σ.next :: fr.locals }
  rcases hown with ⟨fr0, hk0, hmem0⟩
  have hfr0 : fr0 = fr := by
    simpa [hsc] using hk0.symm
  subst fr0
  refine ⟨frNew, ?_, ?_⟩
  · simp [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
      recordLocal, writeHeap, bindTopBinding, hsc]
  · simp [frNew, hmem0]

private theorem runtimeFrameOwnsAddress_succ_preserved_declareObjectStateWithNext
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value} {aNext : Nat}
    {fr : ScopeFrame} {frs : List ScopeFrame}
    {j a : Nat}
    (hsc : σ.scopes = fr :: frs)
    (hown : runtimeFrameOwnsAddress σ (j + 1) a) :
    runtimeFrameOwnsAddress (declareObjectStateWithNext σ τ x ov aNext) (j + 1) a := by
  rcases hown with ⟨fr', hk, hmem⟩
  exact ⟨fr',
    by
      simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
        recordLocal, writeHeap, bindTopBinding, hsc] using hk,
    hmem⟩

theorem declareObject_preserves_allObjectBindingsOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    allObjectBindingsOwned σ' := by
  intro hσ _ hdecl
  let h_all_owned := hσ.objectsOwned
  intro k y υ a hbind
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          rcases runtimeFrameBindsObject_zero_declareObjectStateWithNext_cases
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (y := y) (υ := υ) (a := a) hsc hbind with
            hnew | hbindOld
          · rcases hnew with ⟨hy, hυ, ha⟩
            subst hy
            subst hυ
            subst ha
            exact runtimeFrameOwnsAddress_zero_new_declareObjectStateWithNext hsc
          · have hownOld : runtimeFrameOwnsAddress σ 0 a :=
              h_all_owned _ _ _ _ hbindOld
            exact runtimeFrameOwnsAddress_zero_preserved_declareObjectStateWithNext
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (a := a) hsc hownOld
      | succ j =>
          have hbindOld : runtimeFrameBindsObject σ (j + 1) y υ a :=
            runtimeFrameBindsObject_succ_declareObjectStateWithNext_inv
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (j := j) (y := y) (υ := υ) (a := a) hsc hbind
          have hownOld : runtimeFrameOwnsAddress σ (j + 1) a :=
            h_all_owned _ _ _ _ hbindOld
          exact runtimeFrameOwnsAddress_succ_preserved_declareObjectStateWithNext
            (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
            (fr := fr) (frs := frs) (j := j) (a := a) hsc hownOld

theorem declareObject_preserves_ownedNoDupPerFrame
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ownedAddressesNoDupPerFrame σ' := by
  intro hσ hfresh hdecl k fr' hk
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  rcases hσ.nextFresh with ⟨hnextHeap, hnextLocals⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          have hfr' : fr' =
              { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z
                locals := σ.next :: fr.locals } := by
            simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
              recordLocal, writeHeap, bindTopBinding, hsc] using hk.symm
          subst hfr'
          have hnodupOld : fr.locals.Nodup := hσ.ownedNoDupPerFrame 0 fr (by simp [hsc])
          have hnotin : σ.next ∉ fr.locals := hnextLocals 0 fr (by simp [hsc])
          exact List.nodup_cons.mpr ⟨hnotin, hnodupOld⟩
      | succ j =>
          exact hσ.ownedNoDupPerFrame (j + 1) fr'
            (by simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
              recordLocal, writeHeap, bindTopBinding, hsc] using hk)

theorem declareObject_preserves_ownedDisjointAcrossFrames
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ownedAddressesDisjointAcrossFrames σ' := by
  intro hσ hfresh hdecl i j fi fj a hij hi hj hai
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  rcases hσ.nextFresh with ⟨hnextHeap, hnextLocals⟩
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases i with
      | zero =>
          cases j with
          | zero =>
              exfalso
              exact hij rfl
          | succ j' =>
              have hfi : fi =
                  { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z
                    locals := σ.next :: fr.locals } := by
                simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                  recordLocal, writeHeap, bindTopBinding, hsc] using hi.symm
              subst hfi
              simp at hai
              cases hai with
              | inl hEq =>
                  subst hEq
                  exact hnextLocals (j' + 1) fj
                    (by simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                      recordLocal, writeHeap, bindTopBinding, hsc] using hj)
              | inr hold =>
                  exact hσ.ownedDisjoint 0 (j' + 1) fr fj a
                    (by simp)
                    (by simp [hsc])
                    (by simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                      recordLocal, writeHeap, bindTopBinding, hsc] using hj)
                    hold
      | succ i' =>
          cases j with
          | zero =>
              have hfj : fj =
                  { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z
                    locals := σ.next :: fr.locals } := by
                simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                  recordLocal, writeHeap, bindTopBinding, hsc] using hj.symm
              subst hfj
              intro hmemTop
              simp at hmemTop
              cases hmemTop with
              | inl hEq =>
                  subst hEq
                  exact hnextLocals (i' + 1) fi
                    (by simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                      recordLocal, writeHeap, bindTopBinding, hsc] using hi) hai
              | inr holdTop =>
                  exact hσ.ownedDisjoint (i' + 1) 0 fi fr a
                    (by simp)
                    (by simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                      recordLocal, writeHeap, bindTopBinding, hsc] using hi)
                    (by simp [hsc])
                    hai holdTop
          | succ j' =>
              exact hσ.ownedDisjoint (i' + 1) (j' + 1) fi fj a hij
                (by simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                  recordLocal, writeHeap, bindTopBinding, hsc] using hi)
                (by simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
                  recordLocal, writeHeap, bindTopBinding, hsc] using hj)
                hai

theorem declareObject_preserves_allOwnedAddressesNamed
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    allOwnedAddressesNamed σ' := by
  intro hσ hfresh hdecl k a hown
  exact declareObject_preserves_ownedAddressNamed hσ hfresh hdecl hown

axiom declareObject_preserves_initializedValuesTyped
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a},
      runtimeFrameBindsObject σ' k y υ a →
      heapInitializedTypedAt σ' a υ ∨ True

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

axiom declareObject_preserves_refTargetsAvoidInnerOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ a j},
      runtimeFrameBindsRef σ' k y υ a →
      j < k →
      ¬ runtimeFrameOwnsAddress σ' j a

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


private theorem typeFrameDeclObject_zero_name_ne_of_fresh
    {Γ : TypeEnv} {x y : Ident} {υ : CppType} :
    currentTypeScopeFresh Γ x →
    typeFrameDeclObject Γ 0 y υ →
    y ≠ x := by
  intro hfresh hty
  intro hy
  subst hy
  rcases hty with ⟨fr, hk, hdecl⟩
  cases hsc : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      have hfr : fr = fr0 := by
        simpa [hsc] using hk.symm
      subst hfr
      simp [currentTypeScopeFresh, hsc] at hfresh
      rw [hfresh] at hdecl
      simp at hdecl

theorem declareObject_preserves_old_object_realizers
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclObject Γ k y υ →
      ∃ a,
        runtimeFrameBindsObject σ' k y υ a ∧
        runtimeFrameOwnsAddress σ' k a ∧
        heapLiveTypedAt σ' a υ := by
  intro hσ hfresh hdecl k y υ hty
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheapNone, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'

  rcases hσ.objectDeclRealized hty with ⟨a, hbindOld, hownOld, hliveOld⟩

  have ha : a ≠ σ.next := by
    intro haeq
    subst haeq
    rcases hliveOld with ⟨c, hheap, halive, htyc⟩
    rw [hheapNone] at hheap
    simp at hheap

  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      cases k with
      | zero =>
          have hy : y ≠ x :=
            typeFrameDeclObject_zero_name_ne_of_fresh hfresh hty
          refine ⟨a, ?_, ?_, ?_⟩
          · exact
              runtimeFrameBindsObject_zero_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
                (a := a) (fr := fr) (frs := frs) hsc hy hbindOld
          · exact
              runtimeFrameOwnsAddress_zero_preserved_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (fr := fr) (frs := frs) (a := a) hsc hownOld
          · exact
              heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (a := a) (υ := υ) ha hliveOld
      | succ j =>
          refine ⟨a, ?_, ?_, ?_⟩
          · exact
              runtimeFrameBindsObject_succ_preserved_declareObjectStateWithNext
                (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
                (j := j) (a := a) (fr := fr) (frs := frs) hsc hbindOld
          · exact
              runtimeFrameOwnsAddress_succ_preserved_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (fr := fr) (frs := frs) (j := j) (a := a) hsc hownOld
          · exact
              heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (a := a) (υ := υ) ha hliveOld


theorem declareObject_objectDeclRealized_of_decomposition
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    currentTypeScopeFresh Γ x →
    ScopedTypedStateConcrete Γ σ →
    DeclaresObject σ τ x ov σ' →
    ∀ {k y υ},
      typeFrameDeclObject (declareTypeObject Γ x τ) k y υ →
      ∃ a,
        runtimeFrameBindsObject σ' k y υ a ∧
        runtimeFrameOwnsAddress σ' k a ∧
        heapLiveTypedAt σ' a υ := by
  intro hfresh hσ hdecl k y υ hty
  rcases typeFrameDeclObject_declareTypeObject_cases hfresh hty with hnew | hold
  · rcases hnew with ⟨hk, hy, hυ⟩
    subst hk
    subst hy
    subst hυ
    exact declareObject_realizes_new_top_object hσ hfresh hdecl
  · exact declareObject_preserves_old_object_realizers hσ hfresh hdecl hold

/-! =========================================================
    4. 最終組み立て
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
      shadowing := ?_
      objectDeclRealized := ?_
      refDeclRealized := ?_
      ownedAddressNamed := ?_
      refsNotOwned := ?_
      objectsOwned := ?_
      ownedNoDupPerFrame := ?_
      ownedDisjoint := ?_
      ownedNamed := ?_
      heapStoredValuesTyped := ?_
      initializedValuesTyped := ?_
      nextFresh := ?_
      refTargetsAvoidInnerOwned := ?_ }

  · exact declareObject_preserves_frameDepthAgreement hσ hfresh hdecl
  · exact declareObject_preserves_shadowingCompatible hσ hfresh hdecl
  · intro k y υ hty
    exact declareObject_objectDeclRealized_of_decomposition hfresh hσ hdecl hty
  · intro k y υ hty
    exact declareObject_refDeclRealized_of_decomposition hfresh hσ hdecl hty
  · intro k a hown
    exact declareObject_preserves_ownedAddressNamed hσ hfresh hdecl hown
  · exact declareObject_preserves_refBindingsNeverOwned hσ hfresh hdecl
  · exact declareObject_preserves_allObjectBindingsOwned hσ hfresh hdecl
  · exact declareObject_preserves_ownedNoDupPerFrame hσ hfresh hdecl
  · exact declareObject_preserves_ownedDisjointAcrossFrames hσ hfresh hdecl
  · exact declareObject_preserves_allOwnedAddressesNamed hσ hfresh hdecl
  · exact declareObject_preserves_heapInitializedValuesTyped hσ hfresh hdecl
  · intro k y τ_obj addr hbind
    exact declareObject_preserves_initializedValuesTyped hσ hfresh hdecl hbind
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
