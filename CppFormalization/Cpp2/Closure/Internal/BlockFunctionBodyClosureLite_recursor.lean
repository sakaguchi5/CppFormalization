import CppFormalization.Cpp2.Closure.Internal.BlockBodyFunctionClosureLite
import CppFormalization.Cpp2.Closure.Internal.Transport.BlockBodyBoundaryTransportLite
import CppFormalization.Cpp2.Lemmas.RuntimeState
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp
namespace BlockFunctionBodyClosureLite

@[simp] theorem pushScope_scopes_length
    (σ : State) :
    (pushScope σ).scopes.length = σ.scopes.length + 1 := by
  simp [pushScope]

theorem declareRefState_scopes_length_of_nonempty
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hne : σ.scopes ≠ []) :
    (declareRefState σ τ x a).scopes.length = σ.scopes.length := by
  unfold declareRefState bindTopBinding
  cases hsc : σ.scopes with
  | nil =>
      contradiction
  | cons fr frs =>
      simp

theorem declareObjectStateCore_scopes_length_of_nonempty
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hne : σ.scopes ≠ []) :
    (declareObjectStateCore σ τ x ov).scopes.length = σ.scopes.length := by
  unfold declareObjectStateCore bindTopBinding writeHeap recordLocal
  cases hsc : σ.scopes with
  | nil =>
      contradiction
  | cons fr frs =>
      simp

theorem declaresObject_scopes_length_of_nonempty
    {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hdecl : DeclaresObject σ τ x ov σ')
    (hne : σ.scopes ≠ []) :
    σ'.scopes.length = σ.scopes.length := by
  rcases hdecl with ⟨aNext, hwithNext⟩
  rcases hwithNext with ⟨σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨_hobj, _hfresh, _hheap, _hovcompat, hcore⟩
  rcases hpolicy with ⟨_hpostFresh, hσ'⟩
  subst σcore
  subst σ'
  simpa [setNext] using
    (declareObjectStateCore_scopes_length_of_nonempty
      (σ := σ) (τ := τ) (x := x) (ov := ov) hne)

theorem closeScope_scopes_length_pred
    {σ σ' : State}
    (hclose : CloseScope σ σ') :
    σ'.scopes.length + 1 = σ.scopes.length := by
  unfold CloseScope at hclose
  cases hsc : σ.scopes with
  | nil =>
      simp [popScope?, hsc] at hclose
  | cons fr frs =>
      simp [popScope?, hsc] at hclose
      subst σ'
      simp [scopes_killLocals]

private theorem nonempty_of_same_scope_length
    {σ σ' : State}
    (hlen : σ'.scopes.length = σ.scopes.length)
    (hne : σ.scopes ≠ []) :
    σ'.scopes ≠ [] := by
  cases hsc' : σ'.scopes with
  | nil =>
      simp [hsc'] at hlen
      cases hsc : σ.scopes with
      | nil =>
          contradiction
      | cons fr frs =>
          simp [hsc] at hlen
  | cons fr frs =>
      simp

theorem stmt_preserves_scope_length_of_nonempty
    {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult}
    (h : BigStepStmt σ st ctrl σ') :
    σ.scopes ≠ [] → σ'.scopes.length = σ.scopes.length := by
  exact
    BigStepStmt.rec
      (motive_1 := fun {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
        (_h : BigStepStmt σ st ctrl σ') =>
          σ.scopes ≠ [] → σ'.scopes.length = σ.scopes.length)
      (motive_2 := fun {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
        (_h : BigStepBlock σ ss ctrl σ') =>
          σ.scopes ≠ [] → σ'.scopes.length = σ.scopes.length)
      (skip := by intro σ hne; rfl)
      (expr := by intro σ e v hval hne; rfl)
      (assign := by
        intro σ σ' p e v hval hassign hne
        rcases hassign with ⟨a, c, _, _, _, _, rfl⟩
        simp [scopes_writeHeap])
      (declareObjNone := by
        intro σ σ' τ x hdecl hne
        exact declaresObject_scopes_length_of_nonempty hdecl hne)
      (declareObjSome := by
        intro σ σ' τ x e v hval hdecl hne
        exact declaresObject_scopes_length_of_nonempty hdecl hne)
      (declareRef := by
        intro σ σ' τ x p a hplace href hne
        rcases href with ⟨_, c, _, _, _, rfl⟩
        exact declareRefState_scopes_length_of_nonempty hne)
      (seqNormal := by
        intro σ σ₁ σ₂ s t ctrl hstepS hstepT ihS ihT hne
        have hlenS := ihS hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenS hne
        have hlenT := ihT hne₁
        exact Eq.trans hlenT hlenS)
      (seqBreak := by intro σ σ₁ s t hstepS ihS hne; exact ihS hne)
      (seqContinue := by intro σ σ₁ s t hstepS ihS hne; exact ihS hne)
      (seqReturn := by intro σ σ₁ s t rv hstepS ihS hne; exact ihS hne)
      (iteTrue := by intro σ σ' c s t ctrl hcond hstepS ihS hne; exact ihS hne)
      (iteFalse := by intro σ σ' c s t ctrl hcond hstepT ihT hne; exact ihT hne)
      (whileFalse := by intro σ c body hcond hne; rfl)
      (whileTrueNormal := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail hne
        have hlenBody := ihBody hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenBody hne
        have hlenTail := ihTail hne₁
        exact Eq.trans hlenTail hlenBody)
      (whileTrueBreak := by intro σ σ₁ c body hcond hbody ihBody hne; exact ihBody hne)
      (whileTrueContinue := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail hne
        have hlenBody := ihBody hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenBody hne
        have hlenTail := ihTail hne₁
        exact Eq.trans hlenTail hlenBody)
      (whileTrueReturn := by intro σ σ₁ c body rv hcond hbody ihBody hne; exact ihBody hne)
      (block := by
        intro σ σ₀ σ₁ σ₂ ss ctrl hopen hbody hclose ihBody hne
        cases hopen
        have hnePush : (pushScope σ).scopes ≠ [] := by
          simp [pushScope]
        have hlenBody : σ₁.scopes.length = (pushScope σ).scopes.length := ihBody hnePush
        have hlenClose : σ₂.scopes.length + 1 = σ₁.scopes.length :=
          closeScope_scopes_length_pred hclose
        have htmp : σ₂.scopes.length + 1 = σ.scopes.length + 1 := by
          calc
            σ₂.scopes.length + 1 = σ₁.scopes.length := hlenClose
            _ = (pushScope σ).scopes.length := hlenBody
            _ = σ.scopes.length + 1 := pushScope_scopes_length σ
        exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using htmp))
      (breakStmt := by intro σ hne; rfl)
      (continueStmt := by intro σ hne; rfl)
      (returnNoneStmt := by intro σ hne; rfl)
      (returnSome := by intro σ e v hval hne; rfl)
      (nil := by intro σ hne; rfl)
      (consNormal := by
        intro σ σ₁ σ₂ s ss ctrl hstepS hstepT ihS ihT hne
        have hlenS := ihS hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenS hne
        have hlenT := ihT hne₁
        exact Eq.trans hlenT hlenS)
      (consBreak := by intro σ σ₁ s ss hstepS ihS hne; exact ihS hne)
      (consContinue := by intro σ σ₁ s ss hstepS ihS hne; exact ihS hne)
      (consReturn := by intro σ σ₁ s ss rv hstepS ihS hne; exact ihS hne)
      h

theorem block_preserves_scope_length_of_nonempty
    {σ σ' : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (h : BigStepBlock σ ss ctrl σ') :
    σ.scopes ≠ [] → σ'.scopes.length = σ.scopes.length := by
  exact
    BigStepBlock.rec
      (motive_1 := fun {σ : State} {st : CppStmt} {ctrl : CtrlResult} {σ' : State}
        (_h : BigStepStmt σ st ctrl σ') =>
          σ.scopes ≠ [] → σ'.scopes.length = σ.scopes.length)
      (motive_2 := fun {σ : State} {ss : StmtBlock} {ctrl : CtrlResult} {σ' : State}
        (_h : BigStepBlock σ ss ctrl σ') =>
          σ.scopes ≠ [] → σ'.scopes.length = σ.scopes.length)
      (skip := by intro σ hne; rfl)
      (expr := by intro σ e v hval hne; rfl)
      (assign := by
        intro σ σ' p e v hval hassign hne
        rcases hassign with ⟨a, c, _, _, _, _, rfl⟩
        simp [scopes_writeHeap])
      (declareObjNone := by
        intro σ σ' τ x hdecl hne
        exact declaresObject_scopes_length_of_nonempty hdecl hne)
      (declareObjSome := by
        intro σ σ' τ x e v hval hdecl hne
        exact declaresObject_scopes_length_of_nonempty hdecl hne)
      (declareRef := by
        intro σ σ' τ x p a hplace href hne
        rcases href with ⟨_, c, _, _, _, rfl⟩
        exact declareRefState_scopes_length_of_nonempty hne)
      (seqNormal := by
        intro σ σ₁ σ₂ s t ctrl hstepS hstepT ihS ihT hne
        have hlenS := ihS hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenS hne
        have hlenT := ihT hne₁
        exact Eq.trans hlenT hlenS)
      (seqBreak := by intro σ σ₁ s t hstepS ihS hne; exact ihS hne)
      (seqContinue := by intro σ σ₁ s t hstepS ihS hne; exact ihS hne)
      (seqReturn := by intro σ σ₁ s t rv hstepS ihS hne; exact ihS hne)
      (iteTrue := by intro σ σ' c s t ctrl hcond hstepS ihS hne; exact ihS hne)
      (iteFalse := by intro σ σ' c s t ctrl hcond hstepT ihT hne; exact ihT hne)
      (whileFalse := by intro σ c body hcond hne; rfl)
      (whileTrueNormal := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail hne
        have hlenBody := ihBody hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenBody hne
        have hlenTail := ihTail hne₁
        exact Eq.trans hlenTail hlenBody)
      (whileTrueBreak := by intro σ σ₁ c body hcond hbody ihBody hne; exact ihBody hne)
      (whileTrueContinue := by
        intro σ σ₁ σ₂ c body ctrl hcond hbody htail ihBody ihTail hne
        have hlenBody := ihBody hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenBody hne
        have hlenTail := ihTail hne₁
        exact Eq.trans hlenTail hlenBody)
      (whileTrueReturn := by intro σ σ₁ c body rv hcond hbody ihBody hne; exact ihBody hne)
      (block := by
        intro σ σ₀ σ₁ σ₂ ss ctrl hopen hbody hclose ihBody hne
        cases hopen
        have hnePush : (pushScope σ).scopes ≠ [] := by
          simp [pushScope]
        have hlenBody : σ₁.scopes.length = (pushScope σ).scopes.length := ihBody hnePush
        have hlenClose : σ₂.scopes.length + 1 = σ₁.scopes.length :=
          closeScope_scopes_length_pred hclose
        have htmp : σ₂.scopes.length + 1 = σ.scopes.length + 1 := by
          calc
            σ₂.scopes.length + 1 = σ₁.scopes.length := hlenClose
            _ = (pushScope σ).scopes.length := hlenBody
            _ = σ.scopes.length + 1 := pushScope_scopes_length σ
        exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using htmp))
      (breakStmt := by intro σ hne; rfl)
      (continueStmt := by intro σ hne; rfl)
      (returnNoneStmt := by intro σ hne; rfl)
      (returnSome := by intro σ e v hval hne; rfl)
      (nil := by intro σ hne; rfl)
      (consNormal := by
        intro σ σ₁ σ₂ s ss ctrl hstepS hstepT ihS ihT hne
        have hlenS := ihS hne
        have hne₁ : σ₁.scopes ≠ [] := nonempty_of_same_scope_length hlenS hne
        have hlenT := ihT hne₁
        exact Eq.trans hlenT hlenS)
      (consBreak := by intro σ σ₁ s ss hstepS ihS hne; exact ihS hne)
      (consContinue := by intro σ σ₁ s ss hstepS ihS hne; exact ihS hne)
      (consReturn := by intro σ σ₁ s ss rv hstepS ihS hne; exact ihS hne)
      h

theorem block_preserves_nonempty_scopes
    {σ σ' : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (h : BigStepBlock σ ss ctrl σ')
    (hne : σ.scopes ≠ []) :
    σ'.scopes ≠ [] := by
  exact nonempty_of_same_scope_length
    (block_preserves_scope_length_of_nonempty h hne) hne

@[simp] theorem bigStepFunctionBlockBody_fellThrough_iff
    {σ σ' : State} {ss : StmtBlock} :
    BigStepFunctionBlockBody σ ss .fellThrough σ' ↔
      BigStepBlock σ ss .normal σ' := by
  constructor
  · intro h
    cases h with
    | fallthrough hblk => exact hblk
  · intro hblk
    exact BigStepFunctionBlockBody.fallthrough hblk

@[simp] theorem bigStepFunctionBlockBody_returned_iff
    {σ σ' : State} {ss : StmtBlock} {rv : Option Value} :
    BigStepFunctionBlockBody σ ss (.returned rv) σ' ↔
      BigStepBlock σ ss (.returnResult rv) σ' := by
  constructor
  · intro h
    cases h with
    | returning hblk => exact hblk
  · intro hblk
    exact BigStepFunctionBlockBody.returning hblk

theorem block_function_body_closure_lite
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    {P : BlockBodyProfileLite (pushTypeScope Γ) ss}
    (h : BodyClosureBoundaryLite Γ σ (.block ss))
    (hprof : h.profile = .block P)
    (hbody :
      ∀ {σ'}, OpenScope σ σ' →
      BlockBodyClosureBoundaryLite (pushTypeScope Γ) σ' ss →
      (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨ BigStepStmtDiv σ (.block ss) := by
  let σ₁ := pushScope σ
  have hopen : OpenScope σ σ₁ := by
    rfl
  have hopened : BlockBodyClosureBoundaryLite (pushTypeScope Γ) σ₁ ss :=
    BlockBodyBoundaryTransportLite.blockBodyBoundaryLite_of_bodyClosureBoundaryLite_opened
      h hprof hopen
  rcases hbody hopen hopened with hterm | hdiv
  · rcases hterm with ⟨ex, σ₂, hfb⟩
    cases ex with
    | fellThrough =>
        have hblk : BigStepBlock σ₁ ss .normal σ₂ := by
          simpa using hfb
        have hnePush : σ₁.scopes ≠ [] := by
          simp [σ₁, pushScope]
        have hne₂ : σ₂.scopes ≠ [] :=
          block_preserves_nonempty_scopes hblk hnePush
        have hexClose : ∃ σ₃, CloseScope σ₂ σ₃ := by
          simpa [closeScope_eq_popScope] using (popScope?_some_iff σ₂).2 hne₂
        rcases hexClose with ⟨σ₃, hclose⟩
        left
        refine ⟨.fellThrough, σ₃, ?_⟩
        apply BigStepFunctionBody.fallthrough
        exact BigStepStmt.block hopen hblk hclose
    | returned rv =>
        have hblk : BigStepBlock σ₁ ss (.returnResult rv) σ₂ := by
          simpa using hfb
        have hnePush : σ₁.scopes ≠ [] := by
          simp [σ₁, pushScope]
        have hne₂ : σ₂.scopes ≠ [] :=
          block_preserves_nonempty_scopes hblk hnePush
        have hexClose : ∃ σ₃, CloseScope σ₂ σ₃ := by
          simpa [closeScope_eq_popScope] using (popScope?_some_iff σ₂).2 hne₂
        rcases hexClose with ⟨σ₃, hclose⟩
        left
        refine ⟨.returned rv, σ₃, ?_⟩
        apply BigStepFunctionBody.returning
        exact BigStepStmt.block hopen hblk hclose
  · right
    exact BigStepStmtDiv.block hopen hdiv

end BlockFunctionBodyClosureLite
end Cpp
