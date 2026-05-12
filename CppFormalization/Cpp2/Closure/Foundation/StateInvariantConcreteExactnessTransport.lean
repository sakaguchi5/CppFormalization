import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteStrengthening
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Lemmas.TypeEnv
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCore

namespace Cpp

private theorem topFrameBindingFresh_of_currentScopeFresh
    {σ : State} {x : Ident} :
    currentScopeFresh σ x →
    topFrameBindingFresh σ x := by
  intro hfresh fr hσ0
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hfresh
  | cons fr0 frs =>
      simp [currentScopeFresh, hsc] at hfresh
      simp [hsc] at hσ0
      subst fr
      exact hfresh

private theorem frameDeclBindingExactAt_insertTopDecl_bindTopBinding
    {Γfr : TypeFrame} {σfr : ScopeFrame}
    {x : Ident} {d : DeclInfo} {b : Binding}
    (hexact : frameDeclBindingExactAt Γfr σfr)
    (hΓfresh : Γfr.decls x = none)
    (hσfresh : σfr.binds x = none)
    (hmatchxb : DeclMatchesBinding d b)
    {ls : List Nat} :
    frameDeclBindingExactAt
      ({ Γfr with decls := fun y => if y = x then some d else Γfr.decls y })
      ({ σfr with binds := fun y => if y = x then some b else σfr.binds y, locals := ls }) := by
  constructor
  · intro y d' hdecl
    by_cases hy : y = x
    · subst hy
      refine ⟨b, ?_, ?_⟩
      · simp
      · have hd : d' = d := by
          simpa using hdecl.symm
        subst hd
        exact hmatchxb
    · have hdeclOld : Γfr.decls y = some d' := by
        simpa [hy] using hdecl
      rcases frameDeclBindingExactAt_forward hexact hdeclOld with ⟨b', hb', hmatch⟩
      exact ⟨b', by simpa [hy] using hb', hmatch⟩
  · intro y b' hbind
    by_cases hy : y = x
    · subst hy
      refine ⟨d, ?_, ?_⟩
      · simp
      · have hb : b' = b := by
          simpa using hbind.symm
        subst hb
        exact hmatchxb
    · have hbindOld : σfr.binds y = some b' := by
        simpa [hy] using hbind
      rcases frameDeclBindingExactAt_backward hexact hbindOld with ⟨d', hdecl, hmatch⟩
      exact ⟨d', by simpa [hy] using hdecl, hmatch⟩


/-! =========================================================
    Declaration exactness / shadowing / frame-depth transport
    ========================================================= -/

/-- Type declaration updates preserve all deeper type scopes. -/
@[simp] theorem declareTypeObject_scopes_succ
    {Γ : TypeEnv} {x : Ident} {τ : CppType} {k : Nat} :
    (declareTypeObject Γ x τ).scopes[k.succ]? = Γ.scopes[k.succ]? := by
  cases hsc : Γ.scopes <;> simp [declareTypeObject, insertTopDecl, hsc]

/-- Ref declaration updates preserve all deeper type scopes. -/
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
    simp [declareTypeObject, insertTopDecl,
      declareObjectState, declareObjectStateWithNext, setNext,
      declareObjectStateCore, recordLocal, bindTopBinding, writeHeap,
      hG, hS] at *
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

/--
Top-frame exactness update for an object declaration, with the type-side top
frame supplied explicitly.  This is the assembly-facing version; the
`currentTypeScopeFresh` variants below remain the more canonical exported form.
-/
theorem framewiseDeclBindingExact_declareTypeObject_declareObjectState_from_topFrameFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value}
    {Γtop : TypeFrame} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    Γ.scopes[0]? = some Γtop →
    Γtop.decls x = none →
    topFrameBindingFresh σ x →
    framewiseDeclBindingExact (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  intro hdepth hexact hΓ0 hfreshType hfreshRuntime
  intro k Γfr σfr hkΓ hkσ
  cases hG : Γ.scopes with
  | nil =>
      simp [hG] at hΓ0
  | cons Γtop0 Γrest =>
      cases hS : σ.scopes with
      | nil =>
          unfold frameDepthAgreement at hdepth
          simp [hG, hS] at hdepth
      | cons σtop σrest =>
          cases k with
          | zero =>
              have hExact0 : frameDeclBindingExactAt Γtop0 σtop :=
                hexact 0 Γtop0 σtop (by simp [hG]) (by simp [hS])
              have hΓtopEq : Γtop0 = Γtop := by
                simpa [hG] using hΓ0
              rw [hΓtopEq] at hExact0
              have hTypeFresh0 : Γtop.decls x = none := hfreshType
              have hRunFresh0 : σtop.binds x = none :=
                hfreshRuntime σtop (by simp [hS])
              have hTop :
                  frameDeclBindingExactAt
                    { Γtop with
                      decls := fun y =>
                        if y = x then some (.object τ) else Γtop.decls y }
                    { σtop with
                      binds := fun y =>
                        if y = x then some (.object τ σ.next) else σtop.binds y,
                      locals := σ.next :: σtop.locals } :=
                frameDeclBindingExactAt_insertTopDecl_bindTopBinding
                  (hexact := hExact0)
                  (hΓfresh := hTypeFresh0)
                  (hσfresh := hRunFresh0)
                  (hmatchxb := by simp [DeclMatchesBinding])
                  (ls := σ.next :: σtop.locals)
              have hΓfr :
                  Γfr =
                    { Γtop with
                      decls := fun y =>
                        if y = x then some (.object τ) else Γtop.decls y } := by
                simp [declareTypeObject, insertTopDecl, hG] at hkΓ
                rw [hΓtopEq] at hkΓ
                exact hkΓ.symm
              rcases declareObjectState_lookup_zero_frame_of_cons
                (σ := σ) (τ := τ) (x := x) (ov := ov)
                (fr0 := σtop) (frs := σrest) hS hkσ with rfl
              rw [hΓfr]
              exact hTop
          | succ j =>
              have hkΓOld : Γ.scopes[j.succ]? = some Γfr := by
                simpa [declareTypeObject, insertTopDecl, hG] using hkΓ
              have hkσOld : σ.scopes[j.succ]? = some σfr :=
                (declareObjectState_lookup_succ_iff).1 hkσ
              exact hexact j.succ Γfr σfr hkΓOld hkσOld

theorem framewiseDeclBindingExact_declareTypeRef_declareRefState_from_topFrameFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {a : Nat}
    {Γtop : TypeFrame} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    Γ.scopes[0]? = some Γtop →
    Γtop.decls x = none →
    topFrameBindingFresh σ x →
    framewiseDeclBindingExact (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  intro hdepth hexact hΓ0 hfreshType hfreshRuntime
  intro k Γfr σfr hkΓ hkσ
  cases hG : Γ.scopes with
  | nil =>
      simp [hG] at hΓ0
  | cons Γtop0 Γrest =>
      cases hS : σ.scopes with
      | nil =>
          unfold frameDepthAgreement at hdepth
          simp [hG, hS] at hdepth
      | cons σtop σrest =>
          cases k with
          | zero =>
              have hExact0 : frameDeclBindingExactAt Γtop0 σtop :=
                hexact 0 Γtop0 σtop (by simp [hG]) (by simp [hS])
              have hΓtopEq : Γtop0 = Γtop := by
                simpa [hG] using hΓ0
              rw [hΓtopEq] at hExact0
              have hTypeFresh0 : Γtop.decls x = none := hfreshType
              have hRunFresh0 : σtop.binds x = none :=
                hfreshRuntime σtop (by simp [hS])
              have hTop :
                  frameDeclBindingExactAt
                    { Γtop with
                      decls := fun y => if y = x then some (.ref τ) else Γtop.decls y }
                    { σtop with
                      binds := fun y => if y = x then some (.ref τ a) else σtop.binds y } :=
                frameDeclBindingExactAt_insertTopDecl_bindTopBinding
                  (hexact := hExact0)
                  (hΓfresh := hTypeFresh0)
                  (hσfresh := hRunFresh0)
                  (hmatchxb := by simp [DeclMatchesBinding])
                  (ls := σtop.locals)
              have hΓfr :
                  Γfr =
                    { Γtop with
                      decls := fun y => if y = x then some (.ref τ) else Γtop.decls y } := by
                simp [declareTypeRef, insertTopDecl, hG] at hkΓ
                rw [hΓtopEq] at hkΓ
                exact hkΓ.symm
              have hσfr :
                  σfr =
                    { σtop with
                      binds := fun y => if y = x then some (.ref τ a) else σtop.binds y } := by
                simp [declareRefState, bindTopBinding, hS] at hkσ
                exact hkσ.symm
              rw [hΓfr, hσfr]
              exact hTop
          | succ j =>
              have hkΓOld : Γ.scopes[j.succ]? = some Γfr := by
                simpa [declareTypeRef, insertTopDecl, hG] using hkΓ
              have hkσOld : σ.scopes[j.succ]? = some σfr := by
                simpa [declareRefState, bindTopBinding, hS] using hkσ
              exact hexact j.succ Γfr σfr hkΓOld hkσOld

theorem framewiseDeclBindingExact_declareTypeObject_declareObjectStateWithNext
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value} {aNext : Nat}
    {Γtop : TypeFrame} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    Γ.scopes[0]? = some Γtop →
    Γtop.decls x = none →
    topFrameBindingFresh σ x →
    framewiseDeclBindingExact
      (declareTypeObject Γ x τ)
      (declareObjectStateWithNext σ τ x ov aNext) := by
  intro hdepth hexact hΓ0 hfreshType hfreshRuntime
  have hold :
      framewiseDeclBindingExact
        (declareTypeObject Γ x τ)
        (declareObjectState σ τ x ov) :=
    framewiseDeclBindingExact_declareTypeObject_declareObjectState_from_topFrameFresh
      hdepth hexact hΓ0 hfreshType hfreshRuntime
  intro k Γfr σfr hkΓ hkσ
  have hkσOld : (declareObjectState σ τ x ov).scopes[k]? = some σfr := by
    simpa [scopes_declareObjectStateWithNext_eq_declareObjectState] using hkσ
  exact hold k Γfr σfr hkΓ hkσOld

theorem framewiseDeclBindingExact_declareTypeRef_declareRefState_of_topFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    currentTypeScopeFresh Γ x →
    topFrameBindingFresh σ x →
    framewiseDeclBindingExact (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  intro hdepth hexact hΓfresh hσfresh
  intro k Γfr σfr hkΓ hkσ
  cases hG : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hG] at hΓfresh
  | cons Γtop Γrest =>
      cases hS : σ.scopes with
      | nil =>
          simp [frameDepthAgreement, hG, hS] at hdepth
      | cons σtop σrest =>
          cases k with
          | zero =>
              simp [declareTypeRef, insertTopDecl, hG] at hkΓ
              simp [declareRefState, bindTopBinding, hS] at hkσ
              subst Γfr
              subst σfr
              have hExact0 : frameDeclBindingExactAt Γtop σtop :=
                hexact 0 Γtop σtop (by simp [hG]) (by simp [hS])
              have hΓ0fresh : Γtop.decls x = none := by
                simpa [currentTypeScopeFresh, hG] using hΓfresh
              have hσ0fresh : σtop.binds x = none :=
                hσfresh σtop (by simp [hS])
              simpa using
                (frameDeclBindingExactAt_insertTopDecl_bindTopBinding
                  (hexact := hExact0)
                  (hΓfresh := hΓ0fresh)
                  (hσfresh := hσ0fresh)
                  (hmatchxb := by simp [DeclMatchesBinding])
                  (ls := σtop.locals))
          | succ j =>
              have hkΓOld : Γ.scopes[j.succ]? = some Γfr := by
                simpa [declareTypeRef, insertTopDecl, hG] using hkΓ
              have hkσOld : σ.scopes[j.succ]? = some σfr := by
                simpa [declareRefState, bindTopBinding, hS] using hkσ
              exact hexact j.succ Γfr σfr hkΓOld hkσOld

theorem framewiseDeclBindingExact_declareTypeRef_declareRefState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {a : Nat} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    currentTypeScopeFresh Γ x →
    currentScopeFresh σ x →
    framewiseDeclBindingExact (declareTypeRef Γ x τ) (declareRefState σ τ x a) := by
  intro hdepth hexact hΓfresh hσfresh
  exact framewiseDeclBindingExact_declareTypeRef_declareRefState_of_topFresh
    hdepth hexact hΓfresh (topFrameBindingFresh_of_currentScopeFresh hσfresh)

theorem framewiseDeclBindingExact_declareTypeObject_declareObjectState_of_topFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    currentTypeScopeFresh Γ x →
    topFrameBindingFresh σ x →
    framewiseDeclBindingExact (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  intro hdepth hexact hΓfresh hσfresh
  intro k Γfr σfr hkΓ hkσ
  cases hG : Γ.scopes with
  | nil =>
      simp [currentTypeScopeFresh, hG] at hΓfresh
  | cons Γtop Γrest =>
      cases hS : σ.scopes with
      | nil =>
          simp [frameDepthAgreement, hG, hS] at hdepth
      | cons σtop σrest =>
          cases k with
          | zero =>
              simp [declareTypeObject, insertTopDecl, hG] at hkΓ
              rcases declareObjectState_lookup_zero_frame_of_cons hS hkσ with rfl

              subst Γfr

              have hExact0 : frameDeclBindingExactAt Γtop σtop :=
                hexact 0 Γtop σtop (by simp [hG]) (by simp [hS])

              have hΓ0fresh : Γtop.decls x = none := by
                simpa [currentTypeScopeFresh, hG] using hΓfresh

              have hσ0fresh : σtop.binds x = none :=
                hσfresh σtop (by simp [hS])

              simpa using
                (frameDeclBindingExactAt_insertTopDecl_bindTopBinding
                  (hexact := hExact0)
                  (hΓfresh := hΓ0fresh)
                  (hσfresh := hσ0fresh)
                  (hmatchxb := by simp [DeclMatchesBinding])
                  (ls := σ.next :: σtop.locals))

          | succ j =>
              have hkΓOld : Γ.scopes[j.succ]? = some Γfr := by
                simpa [declareTypeObject, insertTopDecl, hG] using hkΓ

              have hkσOld : σ.scopes[j.succ]? = some σfr :=
                (declareObjectState_lookup_succ_iff).1 hkσ

              exact hexact j.succ Γfr σfr hkΓOld hkσOld

theorem framewiseDeclBindingExact_declareTypeObject_declareObjectState
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    currentTypeScopeFresh Γ x →
    currentScopeFresh σ x →
    framewiseDeclBindingExact (declareTypeObject Γ x τ) (declareObjectState σ τ x ov) := by
  intro hdepth hexact hΓfresh hσfresh
  exact framewiseDeclBindingExact_declareTypeObject_declareObjectState_of_topFresh
    hdepth hexact hΓfresh (topFrameBindingFresh_of_currentScopeFresh hσfresh)

theorem framewiseDeclBindingExact_declareTypeObject_declareObjectStateWithNext_of_topFresh
    {Γ : TypeEnv} {σ : State} {x : Ident} {τ : CppType} {ov : Option Value} {aNext : Nat} :
    frameDepthAgreement Γ σ →
    framewiseDeclBindingExact Γ σ →
    currentTypeScopeFresh Γ x →
    topFrameBindingFresh σ x →
    framewiseDeclBindingExact (declareTypeObject Γ x τ) (declareObjectStateWithNext σ τ x ov aNext) := by
  intro hdepth hexact hΓfresh hσfresh
  intro k Γfr σfr hkΓ hkσ
  have hold :=
    framewiseDeclBindingExact_declareTypeObject_declareObjectState_of_topFresh
      (Γ := Γ) (σ := σ) (x := x) (τ := τ) (ov := ov)
      hdepth hexact hΓfresh hσfresh
  have hkσOld : (declareObjectState σ τ x ov).scopes[k]? = some σfr := by
    simpa [scopes_declareObjectStateWithNext_eq_declareObjectState] using hkσ
  exact hold k Γfr σfr hkΓ hkσOld

end Cpp

