import CppFormalization.Cpp2.Closure.Transitions.DeclareObject.RuntimeTransport

namespace Cpp

/-!
# Closure.Transitions.DeclareObject.Realizers

`declareObject` の type-side 分解と old/new realizer 回収をまとめた層。
kernel 側の責務だけを集め、ownership discipline の保存は別ファイルへ分離する。
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
    rcases hliveOld with ⟨c, hheap, htyc, halive⟩
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
              DeclareObjectTransport.runtimeFrameBindsRef_zero_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) (aNext := aNext)
                (υ := υ) (a := a) (fr := fr) (frs := frs) hsc hy hbindOld
          · exact
              DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (a := a) (υ := υ) ha hliveOld
      | succ j =>
          refine ⟨a, ?_, ?_⟩
          · exact
              DeclareObjectTransport.runtimeFrameBindsRef_succ_preserved_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (y := y) (ov := ov) (aNext := aNext)
                (υ := υ) (j := j) (a := a) (fr := fr) (frs := frs) hsc hbindOld
          · exact
              DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
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
    rcases hliveOld with ⟨c, hheap, htyc, halive⟩
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
              DeclareObjectTransport.runtimeFrameBindsObject_zero_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
                (a := a) (fr := fr) (frs := frs) hsc hy hbindOld
          · exact
              DeclareObjectTransport.runtimeFrameOwnsAddress_zero_preserved_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (fr := fr) (frs := frs) (a := a) hsc hownOld
          · exact
              DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (a := a) (υ := υ) ha hliveOld
      | succ j =>
          refine ⟨a, ?_, ?_, ?_⟩
          · exact
              DeclareObjectTransport.runtimeFrameBindsObject_succ_preserved_declareObjectStateWithNext
                (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
                (j := j) (a := a) (fr := fr) (frs := frs) hsc hbindOld
          · exact
              DeclareObjectTransport.runtimeFrameOwnsAddress_succ_preserved_declareObjectStateWithNext
                (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
                (fr := fr) (frs := frs) (j := j) (a := a) hsc hownOld
          · exact
              DeclareObjectTransport.heapLiveTypedAt_preserved_of_ne_declareObjectStateWithNext
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

end Cpp
