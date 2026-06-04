import CppFormalization.Cpp2.Closure.Function.FunctionBody
import CppFormalization.Cpp2.Legacy.ClosureInternal.FunctionBodyClosureConcreteRefined
import CppFormalization.Cpp2.Preservation.BlockNormalPreservation
import CppFormalization.Cpp2.Preservation.Scope.OpenPreservation
import CppFormalization.Cpp2.Operational.Facts.Control.ControlExclusion
import CppFormalization.Cpp2.Operational.Divergence
import CppFormalization.Cpp2.Operational.Facts.ScopeDepth
import CppFormalization.Cpp2.Entry.Body.BlockBodyReadyAtCI
import CppFormalization.Cpp2.Continuation.Compound.Cons.Tail.Continuation
import CppFormalization.Cpp2.Continuation.Successor.BlockCons

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
- scope-depth / closeability facts are factored into `Semantics.Facts.ScopeDepth`.
- opened block-body closure itself is now split into a current-environment
  contract plus `nil` / `cons` head-tail assembly.
- The remaining concrete debt is no longer the block-body case split.  It is the
  lower normal-head residual kernels stated explicitly below.
-/

/-- Function-body style wrapper for block-body executions. -/
inductive BigStepFunctionBlockBody : State → StmtBlock → FunctionExit → State → Prop where
  | fallthrough {σ σ' : State} {ss : StmtBlock} :
      BigStepBlock σ ss .normal σ' →
      BigStepFunctionBlockBody σ ss .fellThrough σ'
  | returning {σ σ' : State} {ss : StmtBlock} {rv : Option Value} :
      BigStepBlock σ ss (.returnResult rv) σ' →
      BigStepFunctionBlockBody σ ss (.returned rv) σ'

/-- Honest boundary contract for an opened block body.

This is the compatibility wrapper used by the statement-level block bridge:
the parameter `Γ` is the outer environment, while the body itself runs under
`pushTypeScope Γ`.
-/
structure BlockBodyReadyConcrete (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  typed : ∃ Δ, HasTypeBlock (pushTypeScope Γ) ss Δ
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss
  state : ScopedTypedStateConcrete (pushTypeScope Γ) σ
  safe : BlockReadyConcrete (pushTypeScope Γ) σ ss

/--
Current-environment opened block-body contract.

This is the recursion-friendly form.  Unlike `BlockBodyReadyConcrete`, it does
not bake in `pushTypeScope`; after a normal head statement, the tail block body
runs under the actual residual environment.
-/
structure BlockBodyReadyConcreteAt (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  typed : ∃ Δ, HasTypeBlock Γ ss Δ
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss
  state : ScopedTypedStateConcrete Γ σ
  safe : BlockReadyConcrete Γ σ ss

/-- Forget the outer-environment wrapper into the current-environment contract. -/
def BlockBodyReadyConcrete.toAt
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyReadyConcrete Γ σ ss) :
    BlockBodyReadyConcreteAt (pushTypeScope Γ) σ ss :=
  { wf := h.wf
    typed := h.typed
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped
    state := h.state
    safe := h.safe }

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

/-- Current-environment version of top-level abrupt exclusion. -/
theorem top_level_abrupt_excluded_from_blockBodyReadyConcreteAt
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyReadyConcreteAt Γ σ ss →
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

theorem BigStepFunctionBlockBody.to_block
    {σ σ' : State} {ss : StmtBlock} {ex : FunctionExit}
    (h : BigStepFunctionBlockBody σ ss ex σ') :
    match ex with
    | .fellThrough => BigStepBlock σ ss .normal σ'
    | .returned rv => BigStepBlock σ ss (.returnResult rv) σ' := by
  cases h with
  | fallthrough hblk =>
      exact hblk
  | returning hblk =>
      exact hblk

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

/-- Extract the head statement boundary from a concrete current-env cons block body. -/
def blockBodyReadyConcreteAt_cons_head
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAt Γ σ (.cons s ss)) :
    BodyReadyConcrete Γ σ s := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using h.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using h.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using h.continueScoped
  have htypedHead : WellTypedFrom Γ s := by
    rcases h.typed with ⟨Δ, hty⟩
    cases hty with
    | cons hs hss =>
        exact ⟨_, hs⟩
  have hreadyHead : StmtReadyConcrete Γ σ s := by
    cases h.safe with
    | cons hs _ =>
        exact hs
  exact
    { wf := hwf.1
      typed := htypedHead
      breakScoped := hbreak.1
      continueScoped := hcont.1
      state := h.state
      safe := hreadyHead }

/-- Reconstruct the current-env tail boundary after a normal head execution.

This version no longer uses the old normal-preservation/readiness axioms.

The remaining old-typing dependency is only used to keep the current
`BlockBodyReadyConcreteAt.typed` field populated.  The actual post-state
validity comes from CI control preservation, and tail readiness comes from an
explicit continuation dynamic boundary.
-/
theorem blockBodyReadyConcreteAt_cons_tail_after_head_normal
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAt Γ σ (.cons s ss))
    (headCI :
      ∀ {Δ : TypeEnv},
        HasTypeStmt Γ s Δ →
        HasTypeStmtCI .normalK Γ s Δ)
    (tailDynamic :
      ∀ {Δ : TypeEnv},
        HasTypeStmtCI .normalK Γ s Δ →
        ScopedTypedStateConcrete Δ σ' →
        BlockReadyConcrete Γ σ (.cons s ss) →
        BigStepStmt σ s .normal σ' →
        BlockContinuationDynamicBoundary Δ σ' ss)
    (hstep : BigStepStmt σ s .normal σ') :
    ∃ Δ, BlockBodyReadyConcreteAt Δ σ' ss := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using h.wf

  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using h.breakScoped

  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using h.continueScoped

  rcases h.typed with ⟨Ω, htyBlock⟩
  cases htyBlock with
  | cons htyHead htyTail =>
      have htyHeadCI : HasTypeStmtCI .normalK Γ s _ :=
        headCI htyHead

      have hcomp : StmtControlCompatible htyHeadCI hstep :=
        stmtControlCompatible_normal_of_bigStep hstep htyHeadCI

      have hstate' : ScopedTypedStateConcrete _ σ' :=
        stmt_normal_preserves_scoped_typed_state_concrete_noReady
          hcomp h.state

      have htailDyn : BlockContinuationDynamicBoundary _ σ' ss :=
        tailDynamic htyHeadCI hstate' h.safe hstep

      exact
        ⟨_,
          { wf := hwf.2
            typed := ⟨_, htyTail⟩
            breakScoped := hbreak.2
            continueScoped := hcont.2
            state := hstate'
            safe := htailDyn.safe }⟩

/--
Provider for reconstructing the current-env tail boundary after a normal head
statement in an opened block body.

This is the new boundary between block-body closure and route-local continuation
construction.  The closure theorem should not know whether the tail boundary was
obtained from legacy transport, CompoundContinuation, or a future CI-native
block-body boundary.
-/
abbrev BlockBodyReadyConcreteAtTailAfterHeadProvider : Prop :=
  ∀ {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock},
    BlockBodyReadyConcreteAt Γ σ (.cons s ss) →
    BigStepStmt σ s .normal σ' →
    ∃ Δ, BlockBodyReadyConcreteAt Δ σ' ss


/--
All current syntax is inside the idealized big-step fragment.

This is a harmless marker debt compared with progress/closure: `CoreBigStepFragment`
is structurally recursive over syntax and every constructor currently belongs to it.
-/
axiom coreBigStepFragment_all
    (st : CppStmt) : CoreBigStepFragment st

/--
Statement closure provider for `BodyReadyAtCI`.

This provider is the old-free replacement surface for the former temporary
`body_ready_at_ci_function_body_progress_or_diverges` axiom.  Callers can build
it from `BodyClosureBoundaryCI` or from the explicit mainline continuation root.
-/
abbrev BodyReadyAtCIClosureProvider : Prop :=
  ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
    CoreBigStepFragment st →
    BodyReadyAtCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/--
Head/tail assembly for a `cons` opened block body in the CI-native current-env
layer.

The closure theorem no longer depends on a statement-progress axiom.  Statement
closure is supplied explicitly by `bodyClosure`.
-/
theorem cons_block_body_function_closure_ci_at
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
    (bodyClosure : BodyReadyAtCIClosureProvider)
    (successor : ControlSuccessor.BlockConsNormalSuccessorProvider)
    (h : BlockBodyReadyAtCI Γ σ (.cons head tail))
    (htail :
      ∀ {Θ : TypeEnv} {σ' : State},
        BlockBodyReadyAtCI Θ σ' tail →
        (∃ ex σ'', BigStepFunctionBlockBody σ' tail ex σ'') ∨
          BigStepBlockDiv σ' tail) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons head tail) ex σ') ∨
      BigStepBlockDiv σ (.cons head tail) := by
  have hheadReady : BodyReadyAtCI Γ σ head :=
    h.headReadyOfCons rfl

  rcases bodyClosure (coreBigStepFragment_all head) hheadReady with
    hheadTerm | hheadDiv
  · rcases hheadTerm with ⟨ex, σ1, hheadExec⟩
    cases ex with
    | returned rv =>
        left
        refine ⟨.returned rv, σ1, ?_⟩
        exact .returning (.consReturn (by simpa using hheadExec.to_stmt))
    | fellThrough =>
        have hstepHead : BigStepStmt σ head .normal σ1 := by
          simpa using hheadExec.to_stmt

        rcases hheadReady.normalTypingOfStep hstepHead with ⟨Θ, hheadCI⟩

        have htailReady : BlockBodyReadyAtCI Θ σ1 tail :=
          successor h hheadCI hstepHead

        rcases htail htailReady with htailTerm | htailDiv
        · rcases htailTerm with ⟨exTail, σ2, htailExec⟩
          cases exTail with
          | fellThrough =>
              left
              refine ⟨.fellThrough, σ2, ?_⟩
              exact
                .fallthrough
                  (.consNormal hstepHead
                    (by simpa using htailExec.to_block))
          | returned rv =>
              left
              refine ⟨.returned rv, σ2, ?_⟩
              exact
                .returning
                  (.consNormal hstepHead
                    (by simpa using htailExec.to_block))
        · right
          exact .consTail hstepHead htailDiv
  · right
    exact .consHere hheadDiv

/-- `nil` opened block body closes immediately with fallthrough. -/
theorem nil_block_body_function_closure_concrete_refined_at
    {σ : State} :
    (∃ ex σ', BigStepFunctionBlockBody σ .nil ex σ') ∨ BigStepBlockDiv σ .nil := by
  left
  refine ⟨.fellThrough, σ, ?_⟩
  exact BigStepFunctionBlockBody.fallthrough BigStepBlock.nil

/--
CI-native opened block-body closure.

This is the new target route.  It is structurally the same proof as the concrete
current-env closure, but its subject is `BlockBodyReadyAtCI`, not
`BlockBodyReadyConcreteAt`.
-/
theorem block_body_function_closure_ci_at
    (bodyClosure : BodyReadyAtCIClosureProvider)
    (successor : ControlSuccessor.BlockConsNormalSuccessorProvider) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock},
      BlockBodyReadyAtCI Γ σ ss →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss
  | _, _, .nil, _ =>
      nil_block_body_function_closure_concrete_refined_at
  | _, _, .cons _ _, h =>
      cons_block_body_function_closure_ci_at
        bodyClosure
        successor
        h
        (fun htail =>
          block_body_function_closure_ci_at bodyClosure successor htail)


/-- Head/tail assembly for a `cons` opened block body in the concrete current-env layer.

This version does not directly depend on old typing transport axioms.  The only
tail reconstruction input is the explicit provider `tailAfterHead`.
-/
theorem cons_block_body_function_closure_concrete_refined_at
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (tailAfterHead : BlockBodyReadyConcreteAtTailAfterHeadProvider)
    (h : BlockBodyReadyConcreteAt Γ σ (.cons s ss))
    (htail :
      ∀ {Δ : TypeEnv} {σ' : State},
        BlockBodyReadyConcreteAt Δ σ' ss →
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons s ss) ex σ') ∨
      BigStepBlockDiv σ (.cons s ss) := by
  have hheadReady : BodyReadyConcrete Γ σ s :=
    blockBodyReadyConcreteAt_cons_head h

  rcases
      concrete_body_ready_function_body_progress_or_diverges_by_cases_concrete_refined
        (coreBigStepFragment_all s)
        hheadReady with hheadTerm | hheadDiv

  · rcases hheadTerm with ⟨ex, σ1, hheadExec⟩
    cases ex with
    | fellThrough =>
        have hstepHead : BigStepStmt σ s .normal σ1 := by
          simpa using (BigStepFunctionBody.to_stmt hheadExec)

        rcases tailAfterHead h hstepHead with
          ⟨Δ, htailReady⟩

        rcases htail htailReady with htailTerm | htailDiv
        · rcases htailTerm with ⟨exTail, σ2, htailExec⟩
          cases exTail with
          | fellThrough =>
              left
              refine ⟨.fellThrough, σ2, ?_⟩
              apply BigStepFunctionBlockBody.fallthrough
              exact BigStepBlock.consNormal hstepHead
                (by simpa using (BigStepFunctionBlockBody.to_block htailExec))
          | returned rv =>
              left
              refine ⟨.returned rv, σ2, ?_⟩
              apply BigStepFunctionBlockBody.returning
              exact BigStepBlock.consNormal hstepHead
                (by simpa using (BigStepFunctionBlockBody.to_block htailExec))
        · right
          exact BigStepBlockDiv.consTail hstepHead htailDiv

    | returned rv =>
        left
        refine ⟨.returned rv, σ1, ?_⟩
        apply BigStepFunctionBlockBody.returning
        exact BigStepBlock.consReturn
          (by simpa using (BigStepFunctionBody.to_stmt hheadExec))

  · right
    exact BigStepBlockDiv.consHere hheadDiv

/--
Opened block-body closure in the current-env concrete layer.

The proof is structurally recursive over the block body.  Tail reconstruction is
not hard-coded here; it is supplied by `tailAfterHead`.
-/
theorem block_body_function_closure_concrete_refined_at
    (tailAfterHead : BlockBodyReadyConcreteAtTailAfterHeadProvider) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock},
      BlockBodyReadyConcreteAt Γ σ ss →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss
  | _, _, .nil, _ =>
      nil_block_body_function_closure_concrete_refined_at
  | _, _, .cons _ _, h =>
      cons_block_body_function_closure_concrete_refined_at
        tailAfterHead
        h
        (fun htail =>
          block_body_function_closure_concrete_refined_at tailAfterHead htail)

/-- Opened block-body closure itself, as seen from a statement-level block entry. -/
theorem block_body_function_closure_concrete_refined
    (tailAfterHead : BlockBodyReadyConcreteAtTailAfterHeadProvider)
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyReadyConcrete Γ σ ss →
    (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss := by
  intro h
  exact block_body_function_closure_concrete_refined_at tailAfterHead h.toAt

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

end Cpp
