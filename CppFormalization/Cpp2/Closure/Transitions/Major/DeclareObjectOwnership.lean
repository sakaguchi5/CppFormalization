import CppFormalization.Cpp2.Closure.Transitions.Major.DeclareObjectTransport

namespace Cpp

/-!
# Closure.Transitions.Major.DeclareObjectOwnership

`declareObject` に対する ownership discipline 側の保存をまとめた層。
`ScopedTypedStateConcreteKernel` に属する realizer 回収は扱わず、
owned / named / disjoint / nodup といった ownership 成分だけを保持する。
-/

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
          rcases DeclareObjectTransport.runtimeFrameOwnsAddress_zero_declareObjectStateWithNext_cases
              (σ := σ) (aNext := aNext) (x := x) (τ := τ) (ov := ov)
              (fr := fr) (frs := frs) hsc hown with
            hnew | hownOld
          · subst hnew
            exact ⟨x, τ,
              DeclareObjectTransport.runtimeFrameBindsObject_zero_new_declareObjectStateWithNext
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
                DeclareObjectTransport.runtimeFrameBindsObject_zero_preserved_of_ne_declareObjectStateWithNext
                  (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
                  (a := a) (fr := fr) (frs := frs) hsc hy hbindOld⟩
      | succ j =>
          have hownOld :
              runtimeFrameOwnsAddress σ (j + 1) a :=
            DeclareObjectTransport.runtimeFrameOwnsAddress_succ_declareObjectStateWithNext_inv
              (σ := σ) (aNext := aNext) (x := x) (τ := τ) (ov := ov)
              (fr := fr) (frs := frs) (j := j) (a := a) hsc hown
          rcases hσ.ownedAddressNamed hownOld with ⟨y, υ, hbindOld⟩
          exact ⟨y, υ,
            DeclareObjectTransport.runtimeFrameBindsObject_succ_preserved_declareObjectStateWithNext
              (σ := σ) (aNext := aNext) (x := x) (y := y) (τ := τ) (υ := υ) (ov := ov)
              (j := j) (a := a) (fr := fr) (frs := frs) hsc hbindOld⟩

theorem declareObject_preserves_refBindingsNeverOwned
    {Γ : TypeEnv} {σ σ' : State}
    {x : Ident} {τ : CppType} {ov : Option Value} :
    ScopedTypedStateConcrete Γ σ →
    currentTypeScopeFresh Γ x →
    DeclaresObject σ τ x ov σ' →
    refBindingsNeverOwned σ' := by
  intro hσ hfresh hdecl k fr' xref τref a hk hbind hlocal
  rcases hdecl with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨hobjTy, hsfresh, hheap0, hovcompat, hcore⟩
  rcases hpolicy with ⟨hcursorFresh, hσ'⟩
  subst σcore
  subst hσ'
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hsfresh
  | cons fr frs =>
      let frNew : ScopeFrame :=
        { binds := fun z => if z = x then some (.object τ σ.next) else fr.binds z
          locals := σ.next :: fr.locals }
      cases k with
      | zero =>
          have hfr' : fr' = frNew := by
            simpa [frNew, declareObjectStateWithNext, setNext, declareObjectStateCore,
              recordLocal, writeHeap, bindTopBinding, hsc] using hk.symm
          subst hfr'
          by_cases ha : a = σ.next
          · refine ⟨x, τ, ?_⟩
            simp [frNew, ha]
          · have hold : a ∈ fr.locals := by
              simpa [frNew, ha] using hlocal
            have hx : xref ≠ x := by
              intro hEq
              subst hEq
              simp [frNew] at hbind
            have hbindOld : fr.binds xref = some (.ref τref a) := by
              simpa [frNew, hx] using hbind
            rcases hσ.refsNotOwned 0 fr xref τref a (by simp [hsc]) hbindOld hold with ⟨y, υ, hyobj⟩
            have hy : y ≠ x := by
              intro hEq
              subst y
              simp [currentScopeFresh, hsc] at hsfresh
              rw [hsfresh] at hyobj
              simp at hyobj
            refine ⟨y, υ, ?_⟩
            simpa [frNew, hy] using hyobj
      | succ j =>
          have hkOld : σ.scopes[j + 1]? = some fr' := by
            simpa [declareObjectStateWithNext, setNext, declareObjectStateCore,
              recordLocal, writeHeap, bindTopBinding, hsc] using hk
          exact hσ.refsNotOwned (j + 1) fr' xref τref a hkOld hbind hlocal

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
          rcases DeclareObjectTransport.runtimeFrameBindsObject_zero_declareObjectStateWithNext_cases
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (y := y) (υ := υ) (a := a) hsc hbind with
            hnew | hbindOld
          · rcases hnew with ⟨hy, hυ, ha⟩
            subst hy
            subst hυ
            subst ha
            exact DeclareObjectTransport.runtimeFrameOwnsAddress_zero_new_declareObjectStateWithNext hsc
          · have hownOld : runtimeFrameOwnsAddress σ 0 a :=
              h_all_owned _ _ _ _ hbindOld
            exact DeclareObjectTransport.runtimeFrameOwnsAddress_zero_preserved_declareObjectStateWithNext
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (a := a) hsc hownOld
      | succ j =>
          have hbindOld : runtimeFrameBindsObject σ (j + 1) y υ a :=
            DeclareObjectTransport.runtimeFrameBindsObject_succ_declareObjectStateWithNext_inv
              (σ := σ) (τ := τ) (x := x) (ov := ov) (aNext := aNext)
              (fr := fr) (frs := frs) (j := j) (y := y) (υ := υ) (a := a) hsc hbind
          have hownOld : runtimeFrameOwnsAddress σ (j + 1) a :=
            h_all_owned _ _ _ _ hbindOld
          exact DeclareObjectTransport.runtimeFrameOwnsAddress_succ_preserved_declareObjectStateWithNext
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

end Cpp
