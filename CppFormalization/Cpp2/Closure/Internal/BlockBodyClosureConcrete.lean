import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureConcreteRefined
import CppFormalization.Cpp2.Closure.Internal.BlockNormalPreservation
import CppFormalization.Cpp2.Closure.Transitions.Scope.OpenPreservation
import CppFormalization.Cpp2.Lemmas.ControlExclusion
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Lemmas.RuntimeState

namespace Cpp

/-!
# Closure.Internal.BlockBodyClosureConcrete

`FunctionBodyClosureConcreteRefined` の block clause は、opened scope の下で
再び `(.block ss)` を再帰する形になっており、意味論的には二重 open を
呼び込む危険がある。

このファイルは、その論点を切り出して、block statement と block body を
分けて扱うための concrete 側補助語彙を導入する。

主眼:
- statement `.block ss` の closure と
- opened scope の下での block body `ss` の closure
を区別する。

更新:
- opened block-body result を statement-level `.block ss` result へ戻す
  open/body/close assembly を theorem 化した。
- high-level `block_function_body_closure_concrete_refined_honest` は、
  もはや axiom ではなく、opened body closure obligation からの assembly theorem である。
-/

/-- Function-body style wrapper for block-body executions. -/
inductive BigStepFunctionBlockBody : State → StmtBlock → FunctionExit → State → Prop where
  | fallthrough {σ σ' : State} {ss : StmtBlock} :
      BigStepBlock σ ss .normal σ' →
      BigStepFunctionBlockBody σ ss .fellThrough σ'
  | returning {σ σ' : State} {ss : StmtBlock} {rv : Option Value} :
      BigStepBlock σ ss (.returnResult rv) σ' →
      BigStepFunctionBlockBody σ ss (.returned rv) σ'

/-- Honest boundary contract for an opened block body. -/
structure BlockBodyReadyConcrete (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  typed : ∃ Δ, HasTypeBlock (pushTypeScope Γ) ss Δ
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss
  state : ScopedTypedStateConcrete (pushTypeScope Γ) σ
  safe : BlockReadyConcrete (pushTypeScope Γ) σ ss

/-- A scoped block body cannot terminate with unresolved `break` / `continue`. -/
theorem top_level_abrupt_excluded_from_blockBodyReadyConcrete
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyReadyConcrete Γ σ ss →
    ¬ BigStepBlock σ ss .breakResult σ' ∧ ¬ BigStepBlock σ ss .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact no_top_break_from_scoped_block hready.breakScoped hbreak
  · intro hcont
    exact no_top_continue_from_scoped_block hready.continueScoped hcont

/-- Block-body level control classification: only fallthrough or return survive. -/
theorem function_block_body_ctrl_classification
    {σ σ' : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (hbreak : BreakWellScopedBlockAt 0 ss)
    (hcont : ContinueWellScopedBlockAt 0 ss)
    (h : BigStepBlock σ ss ctrl σ') :
    ctrl = .normal ∨ ∃ rv, ctrl = .returnResult rv := by
  cases ctrl with
  | normal =>
      exact Or.inl rfl
  | breakResult =>
      exact False.elim (no_top_break_from_scoped_block hbreak h)
  | continueResult =>
      exact False.elim (no_top_continue_from_scoped_block hcont h)
  | returnResult rv =>
      exact Or.inr ⟨rv, rfl⟩

/-- Every well-scoped terminating block body induces a block-body function execution. -/
theorem function_block_body_of_block
    {σ σ' : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (hbreak : BreakWellScopedBlockAt 0 ss)
    (hcont : ContinueWellScopedBlockAt 0 ss)
    (h : BigStepBlock σ ss ctrl σ') :
    ∃ ex, BigStepFunctionBlockBody σ ss ex σ' := by
  rcases function_block_body_ctrl_classification hbreak hcont h with hnorm | ⟨rv, hret⟩
  · refine ⟨.fellThrough, ?_⟩
    exact BigStepFunctionBlockBody.fallthrough (by simpa [hnorm] using h)
  · refine ⟨.returned rv, ?_⟩
    exact BigStepFunctionBlockBody.returning (by simpa [hret] using h)

@[simp] theorem bigStepFunctionBlockBody_fellThrough_iff
    {σ σ' : State} {ss : StmtBlock} :
    BigStepFunctionBlockBody σ ss .fellThrough σ' ↔ BigStepBlock σ ss .normal σ' := by
  constructor
  · intro h
    cases h with
    | fallthrough hblk => simpa using hblk
  · intro h
    exact .fallthrough h

@[simp] theorem bigStepFunctionBlockBody_returned_iff
    {σ σ' : State} {ss : StmtBlock} {rv : Option Value} :
    BigStepFunctionBlockBody σ ss (.returned rv) σ' ↔ BigStepBlock σ ss (.returnResult rv) σ' := by
  constructor
  · intro h
    cases h with
    | returning hblk => simpa using hblk
  · intro h
    exact .returning h


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

@[simp] private theorem pushScope_scopes_length
    (σ : State) :
    (pushScope σ).scopes.length = σ.scopes.length + 1 := by
  simp [pushScope]

private theorem declareRefState_scopes_length_of_nonempty
    {σ : State} {τ : CppType} {x : Ident} {a : Nat}
    (hne : σ.scopes ≠ []) :
    (declareRefState σ τ x a).scopes.length = σ.scopes.length := by
  unfold declareRefState bindTopBinding
  cases hsc : σ.scopes with
  | nil =>
      contradiction
  | cons fr frs =>
      simp

private theorem declareObjectStateCore_scopes_length_of_nonempty
    {σ : State} {τ : CppType} {x : Ident} {ov : Option Value}
    (hne : σ.scopes ≠ []) :
    (declareObjectStateCore σ τ x ov).scopes.length = σ.scopes.length := by
  unfold declareObjectStateCore bindTopBinding writeHeap recordLocal
  cases hsc : σ.scopes with
  | nil =>
      contradiction
  | cons fr frs =>
      simp

private theorem declaresObject_scopes_length_of_nonempty
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

private theorem closeScope_scopes_length_pred
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

private theorem stmt_preserves_scope_length_of_nonempty
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

private theorem block_preserves_scope_length_of_nonempty
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

private theorem block_preserves_nonempty_scopes
    {σ σ' : State} {ss : StmtBlock} {ctrl : CtrlResult}
    (h : BigStepBlock σ ss ctrl σ')
    (hne : σ.scopes ≠ []) :
    σ'.scopes ≠ [] := by
  exact nonempty_of_same_scope_length
    (block_preserves_scope_length_of_nonempty h hne) hne

private theorem killAddr_scopes_eq
    (σ : State) (a : Nat) :
    (killAddr σ a).scopes = σ.scopes := by
  unfold killAddr
  cases h : σ.heap a with
  | none =>
      simp
  | some c =>
      simp [ writeHeap]

private theorem killLocals_scopes_eq
    (σ : State) (as : List Nat) :
    (killLocals σ as).scopes = σ.scopes := by
  induction as generalizing σ with
  | nil =>
      rfl
  | cons a as ih =>
      calc
        (killLocals σ (a :: as)).scopes =
            (killLocals (killAddr σ a) as).scopes := rfl
        _ = (killAddr σ a).scopes := ih (killAddr σ a)
        _ = σ.scopes := killAddr_scopes_eq σ a


private theorem bindTopBinding_scopes_length_eq_of_currentScopeFresh
    {σ : State} {x : Ident} {b : Binding}
    (hfresh : currentScopeFresh σ x) :
    (bindTopBinding σ x b).scopes.length = σ.scopes.length := by
  cases hsc : σ.scopes with
  | nil =>
      simp [currentScopeFresh, hsc] at hfresh
  | cons fr frs =>
      simp [bindTopBinding, hsc]

private theorem recordLocal_scopes_length_eq
    (σ : State) (a : Nat) :
    (recordLocal σ a).scopes.length = σ.scopes.length := by
  cases hsc : σ.scopes with
  | nil =>
      simp [recordLocal, hsc]
  | cons fr frs =>
      simp [recordLocal, hsc]


private theorem opened_block_body_leaves_closable
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

/-- Opening a block statement yields the honest block-body boundary contract. -/
theorem blockBodyReadyConcrete_of_bodyReadyConcrete_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyReadyConcrete Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockBodyReadyConcrete Γ σ' ss := by
  intro hready hopen
  refine {
    wf := by
      simpa [WellFormedStmt] using hready.wf
    typed := by
      rcases hready.typed with ⟨Δ, hty⟩
      cases hty with
      | block hblk =>
          exact ⟨_, hblk⟩
    breakScoped := by
      simpa [BreakWellScoped, BreakWellScopedAt] using hready.breakScoped
    continueScoped := by
      simpa [ContinueWellScoped, ContinueWellScopedAt] using hready.continueScoped
    state := openScope_preserves_scoped_typed_state_concrete hready.state hopen
    safe := block_ready_opened_body hready.safe hopen
  }

/-- Honest next-stage obligation for block-body closure itself. -/
axiom block_body_function_closure_concrete_refined
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyReadyConcrete Γ σ ss →
    (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss

/--
Terminating opened block-body execution assembles into statement-level block execution.
-/
theorem bigStepFunctionBody_block_of_opened_functionBlockBody
    {σ σ0 σ1 : State} {ss : StmtBlock} {ex : FunctionExit}
    (hopen : OpenScope σ σ0)
    (hbody : BigStepFunctionBlockBody σ0 ss ex σ1) :
    ∃ σ2, BigStepFunctionBody σ (.block ss) ex σ2 := by
  cases ex with
  | fellThrough =>
      have hblk : BigStepBlock σ0 ss .normal σ1 := by
        simpa using hbody
      rcases opened_block_body_leaves_closable hopen hblk with ⟨σ2, hclose⟩
      refine ⟨σ2, ?_⟩
      apply BigStepFunctionBody.fallthrough
      exact BigStepStmt.block hopen hblk hclose
  | returned rv =>
      have hblk : BigStepBlock σ0 ss (.returnResult rv) σ1 := by
        simpa using hbody
      rcases opened_block_body_leaves_closable hopen hblk with ⟨σ2, hclose⟩
      refine ⟨σ2, ?_⟩
      apply BigStepFunctionBody.returning
      exact BigStepStmt.block hopen hblk hclose

/-- Divergent opened block-body execution assembles into statement-level block divergence. -/
theorem bigStepStmtDiv_block_of_opened_blockDiv
    {σ σ0 : State} {ss : StmtBlock}
    (hopen : OpenScope σ σ0)
    (hdiv : BigStepBlockDiv σ0 ss) :
    BigStepStmtDiv σ (.block ss) := by
  exact BigStepStmtDiv.block hopen hdiv

/--
Once opened block-body closure is available, block-statement closure follows by
open/body/close assembly.  This is the missing honest bridge: the callback/result
is consumed instead of bypassed.
-/
theorem block_function_body_result_of_opened_block_body_result
    {σ σ0 : State} {ss : StmtBlock}
    (hopen : OpenScope σ σ0)
    (hres : (∃ ex σ', BigStepFunctionBlockBody σ0 ss ex σ') ∨ BigStepBlockDiv σ0 ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss) := by
  rcases hres with hterm | hdiv
  · rcases hterm with ⟨ex, σ1, hbody⟩
    rcases bigStepFunctionBody_block_of_opened_functionBlockBody hopen hbody with ⟨σ2, hstmt⟩
    exact Or.inl ⟨ex, σ2, hstmt⟩
  · exact Or.inr (bigStepStmtDiv_block_of_opened_blockDiv hopen hdiv)

/--
Once block-body closure is available, block-statement closure is derived by
open/body/close assembly rather than by re-running `(.block ss)` under an opened state.
-/
theorem block_function_body_closure_concrete_refined_honest
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyReadyConcrete Γ σ (.block ss) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨ BigStepStmtDiv σ (.block ss) := by
  intro hready
  let σ0 : State := pushScope σ
  have hopen : OpenScope σ σ0 := by
    rfl
  have hopenedReady : BlockBodyReadyConcrete Γ σ0 ss :=
    blockBodyReadyConcrete_of_bodyReadyConcrete_opened hready hopen
  have hres :
      (∃ ex σ', BigStepFunctionBlockBody σ0 ss ex σ') ∨ BigStepBlockDiv σ0 ss :=
    block_body_function_closure_concrete_refined hopenedReady
  exact block_function_body_result_of_opened_block_body_result hopen hres


end Cpp
