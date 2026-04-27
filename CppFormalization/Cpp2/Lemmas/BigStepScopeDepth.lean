import CppFormalization.Cpp2.Lemmas.RuntimeState

/-!
# Cpp2.Lemmas.BigStepScopeDepth

Scope-stack depth facts for the mutually inductive statement/block big-step semantics.

This file centralizes the explicit `BigStepStmt.rec` / `BigStepBlock.rec`
pattern needed for mutually inductive operational derivations.  The closure
layers should import these facts instead of duplicating local recursors.
-/

namespace Cpp

/-- Assignment preserves runtime scope depth. -/
theorem assigns_scopes_length_eq
    {σ σ' : State} {p : PlaceExpr} {v : Value}
    (h : Assigns σ p v σ') :
    σ'.scopes.length = σ.scopes.length := by
  rcases h with ⟨a, c, _hplace, _hheap, _halive, _hcompat, hσ'⟩
  subst σ'
  rfl

/-- Object declaration preserves runtime scope depth whenever it is actually executable. -/
theorem declaresObject_scopes_length_eq
    {σ σ' : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (h : DeclaresObject σ τ x ov σ') :
    σ'.scopes.length = σ.scopes.length := by
  rcases h with ⟨aNext, σcore, hpayload, hpolicy⟩
  rcases hpayload with ⟨_hobj, hfresh, _hheap, _hov, hcore⟩
  rcases hpolicy with ⟨_hcursor, hσ'⟩
  subst σ'
  subst σcore
  cases hs : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hs] at hfresh
  | cons fr frs =>
      simp [setNext, declareObjectStateCore, bindTopBinding, recordLocal, writeHeap, hs]

/-- Reference declaration preserves runtime scope depth whenever it is actually executable. -/
theorem declaresRef_scopes_length_eq
    {σ σ' : State} {τ : CppType} {x : Ident} {a : Nat}
    (h : DeclaresRef σ τ x a σ') :
    σ'.scopes.length = σ.scopes.length := by
  rcases h with ⟨hfresh, _c, _hheap, _hty, _halive, hσ'⟩
  subst σ'
  cases hs : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hs] at hfresh
  | cons fr frs =>
      simp [declareRefState, bindTopBinding, hs]

/-- Closing a scope removes exactly one runtime scope frame. -/
theorem closeScope_scopes_length_eq_succ
    {σ σ' : State}
    (h : CloseScope σ σ') :
    σ.scopes.length = σ'.scopes.length + 1 := by
  unfold CloseScope at h
  cases hs : σ.scopes with
  | nil =>
      simp [popScope?, hs] at h
  | cons fr frs =>
      simp [popScope?, hs] at h
      subst σ'
      simp

/-- A state with a nonempty scope stack can be closed. -/
theorem closeScope_exists_of_scopes_length_pos
    {σ : State}
    (hpos : 0 < σ.scopes.length) :
    ∃ σ', CloseScope σ σ' := by
  cases hs : σ.scopes with
  | nil =>
      simp [hs] at hpos
  | cons fr frs =>
      refine ⟨killLocals { σ with scopes := frs } fr.locals, ?_⟩
      simp [CloseScope, popScope?, hs]

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

theorem nonempty_of_same_scope_length
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

/--
Statement executions preserve runtime scope depth, provided the input stack is nonempty.

The nonempty premise is necessary because the object/reference declaration helper functions
repair an impossible empty stack operationally, while executable declaration semantics rules
also carry freshness premises that rule out the empty current scope.  Keeping the premise
explicit makes the mutual recursor usable for opened block bodies.
-/
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

/-- Block executions preserve runtime scope depth under a nonempty input scope stack. -/
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

/-- A block execution that starts with a nonempty scope stack also ends with one. -/
theorem block_preserves_nonempty_scopes
    {σ σ' : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (h : BigStepBlock σ ss ctrl σ')
    (hne : σ.scopes ≠ []) :
    σ'.scopes ≠ [] := by
  exact nonempty_of_same_scope_length
    (block_preserves_scope_length_of_nonempty h hne) hne

/--
An opened block body always leaves a state that can be closed.

This is the exact operational fact needed by block-statement assembly:
the caller does not need the whole scope-length equality, only the existence
of a post-body `CloseScope`.
-/
theorem opened_block_body_leaves_closable
    {σ σ0 σ1 : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (hopen : OpenScope σ σ0)
    (hbody : BigStepBlock σ0 ss ctrl σ1) :
    ∃ σ2, CloseScope σ1 σ2 := by
  have hne0 : σ0.scopes ≠ [] := by
    cases hopen
    simp [pushScope]
  have hne1 : σ1.scopes ≠ [] :=
    block_preserves_nonempty_scopes hbody hne0
  simpa [closeScope_eq_popScope] using
    (popScope?_some_iff σ1).2 hne1

end Cpp
