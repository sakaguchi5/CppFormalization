import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Proof.Control.BigStepControlCompatibility
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernel

namespace Cpp

/-!
# Closure.Internal.BlockBodyClosureConcreteCI

CI-current opened block-body closure kernel.

This file is the next step after `BlockBodyClosureConcrete` split opened block-body
closure into `nil` / `cons`.

The previous concrete `BlockBodyReadyConcreteAt` still stores old normal typing.
This file introduces the CI-normal current-environment contract and proves the
normal-head residual state/readiness step from the existing CI preservation and
readiness kernels.
-/

/--
Current-environment opened block-body contract with CI normal typing.

This is the recursion-friendly form that should replace the old-typing
`BlockBodyReadyConcreteAt` route once upstream callers can supply CI payloads.
-/
structure BlockBodyReadyConcreteAtCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Prop where
  wf : WellFormedBlock ss
  typed : ∃ Δ, HasTypeBlockCI .normalK Γ ss Δ
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss
  state : ScopedTypedStateConcrete Γ σ
  safe : BlockReadyConcrete Γ σ ss

/-- Current-environment CI version of top-level abrupt exclusion. -/
theorem top_level_abrupt_excluded_from_blockBodyReadyConcreteAtCI
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BlockBodyReadyConcreteAtCI Γ σ ss →
    ¬ BigStepBlock σ ss .breakResult σ' ∧ ¬ BigStepBlock σ ss .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact no_top_break_from_scoped_block hready.breakScoped hbreak
  · intro hcont
    exact no_top_continue_from_scoped_block hready.continueScoped hcont

/-- Extract the head statement boundary from a CI current-env cons block body. -/
def blockBodyReadyConcreteAtCI_cons_head
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss)) :
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
    | cons_normal htyHead htyTail =>
        exact ⟨_, normalCI_to_old_stmt htyHead⟩
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

/--
CI normal preservation for a head statement, routed through the compatibility and
preservation kernels rather than through an old-typing shell.
-/
theorem stmt_normal_preserves_scoped_typed_state_concrete_of_ci
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .normalK Γ s Δ)
    (hσ : ScopedTypedStateConcrete Γ σ)
    (hready : StmtReadyConcrete Γ σ s)
    (hstep : BigStepStmt σ s .normal σ') :
    ScopedTypedStateConcrete Δ σ' := by
  have hcomp : StmtControlCompatible hty hstep :=
    stmtControlCompatible_normal_of_bigStep hstep hty
  exact
    stmt_control_preserves_scoped_typed_state_of_compatible
      mkWhileReentry hcomp hσ hready

/--
CI residual readiness for a cons block after a normal head statement.

This replaces the old-typing residual shell by composing:
1. CI preservation for the head statement;
2. the existing CI block-tail readiness theorem.
-/
theorem cons_block_ready_tail_after_head_normal_ci
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (htyHead : HasTypeStmtCI .normalK Γ s Δ)
    (hσ : ScopedTypedStateConcrete Γ σ)
    (hready : BlockReadyConcrete Γ σ (.cons s ss))
    (hstep : BigStepStmt σ s .normal σ') :
    ScopedTypedStateConcrete Δ σ' ∧ BlockReadyConcrete Δ σ' ss := by
  have hreadyHead : StmtReadyConcrete Γ σ s :=
    cons_block_ready_head hready
  have hσ' : ScopedTypedStateConcrete Δ σ' :=
    stmt_normal_preserves_scoped_typed_state_concrete_of_ci
      mkWhileReentry htyHead hσ hreadyHead hstep
  have hreadyTail : BlockReadyConcrete Δ σ' ss :=
    cons_block_ready_tail_after_head_normal htyHead hσ' hready hstep
  exact ⟨hσ', hreadyTail⟩

/-- Reconstruct the CI current-env tail boundary after a normal head execution. -/
theorem blockBodyReadyConcreteAtCI_cons_tail_after_head_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (hstep : BigStepStmt σ s .normal σ') :
    ∃ Δ, BlockBodyReadyConcreteAtCI Δ σ' ss := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using h.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using h.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using h.continueScoped
  rcases h.typed with ⟨Ω, htyBlock⟩
  cases htyBlock with
  | cons_normal htyHead htyTail =>
      rcases cons_block_ready_tail_after_head_normal_ci
          mkWhileReentry htyHead h.state h.safe hstep with
        ⟨hstate', hreadyTail⟩
      exact
        ⟨_,
          { wf := hwf.2
            typed := ⟨_, htyTail⟩
            breakScoped := hbreak.2
            continueScoped := hcont.2
            state := hstate'
            safe := hreadyTail }⟩

/-- `nil` opened block body closes immediately with fallthrough in the CI route. -/
theorem nil_block_body_function_closure_concrete_refined_at_ci
    {Γ : TypeEnv} {σ : State}
    (_h : BlockBodyReadyConcreteAtCI Γ σ .nil) :
    (∃ ex σ', BigStepFunctionBlockBody σ .nil ex σ') ∨ BigStepBlockDiv σ .nil := by
  left
  refine ⟨.fellThrough, σ, ?_⟩
  exact BigStepFunctionBlockBody.fallthrough BigStepBlock.nil

/-- Head/tail assembly for a `cons` opened block body in the CI current-env route. -/
theorem cons_block_body_function_closure_concrete_refined_at_ci
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (htail :
      ∀ {Δ : TypeEnv} {σ' : State},
        BlockBodyReadyConcreteAtCI Δ σ' ss →
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons s ss) ex σ') ∨
      BigStepBlockDiv σ (.cons s ss) := by
  have hheadReady : BodyReadyConcrete Γ σ s :=
    blockBodyReadyConcreteAtCI_cons_head h
  rcases
      concrete_body_ready_function_body_progress_or_diverges_by_cases_concrete_refined
        (coreBigStepFragment_all s)
        hheadReady with hheadTerm | hheadDiv
  · rcases hheadTerm with ⟨ex, σ1, hheadExec⟩
    cases ex with
    | fellThrough =>
        have hstepHead : BigStepStmt σ s .normal σ1 := by
          simpa using (BigStepFunctionBody.to_stmt hheadExec)
        rcases blockBodyReadyConcreteAtCI_cons_tail_after_head_normal
            mkWhileReentry h hstepHead with
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
Opened block-body closure in the CI current-env concrete route.

This is the first version where the normal-head residual state/readiness step is
not an old-typing shell: it is routed through CI preservation and the CI tail
readiness theorem.
-/
theorem block_body_function_closure_concrete_refined_at_ci
    (mkWhileReentry : WhileReentryReadyProvider) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock},
      BlockBodyReadyConcreteAtCI Γ σ ss →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss
  | _, _, .nil, h =>
      nil_block_body_function_closure_concrete_refined_at_ci h
  | _, _, .cons _ _, h =>
      cons_block_body_function_closure_concrete_refined_at_ci mkWhileReentry h
        (fun htail => block_body_function_closure_concrete_refined_at_ci mkWhileReentry htail)

end Cpp
