import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureConcreteRefined
import CppFormalization.Cpp2.Closure.Internal.BlockNormalPreservation
import CppFormalization.Cpp2.Closure.Transitions.Scope.OpenPreservation
import CppFormalization.Cpp2.Lemmas.ControlExclusion
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Lemmas.BigStepScopeDepth

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
- scope-depth / closeability facts are factored into `Lemmas.BigStepScopeDepth`.
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
