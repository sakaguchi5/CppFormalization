import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcreteStrengthening
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Lemmas.TypeEnv
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCore
import CppFormalization.Cpp2.Lemmas.RuntimeObjectCoreWithNext

namespace Cpp
open RuntimeObjectCoreWithNext

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
              simp [declareObjectState, recordLocal, bindTopBinding, hS] at hkσ
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
                  (ls := σ.next :: σtop.locals))
          | succ j =>
              have hkΓOld : Γ.scopes[j.succ]? = some Γfr := by
                simpa [declareTypeObject, insertTopDecl, hG] using hkΓ
              have hkσOld : σ.scopes[j.succ]? = some σfr := by
                simpa [declareObjectState, recordLocal, bindTopBinding, hS] using hkσ
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
    simpa [scopes_declareObjectStateWithNext_eq_old] using hkσ
  exact hold k Γfr σfr hkΓ hkσOld

end Cpp
