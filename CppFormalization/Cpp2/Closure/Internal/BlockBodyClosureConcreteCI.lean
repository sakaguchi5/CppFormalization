import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete
import CppFormalization.Cpp2.Closure.Internal.BlockBodyNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Proof.Control.BigStepControlCompatibility
import CppFormalization.Cpp2.Proof.Preservation.StmtControlKernel

namespace Cpp

/-!
# Closure.Internal.BlockBodyClosureConcreteCI

CI-current opened block-body closure kernel.

This file is the next step after `BlockBodyClosureConcrete` split opened block-body
closure into `nil` / `cons`.

The contract here is profile-aware: it carries the current-environment
normal/return CI block-body profile instead of merely storing one normal typing
payload.  The current theorem-backed route is still intentionally
normal-channel gated, because a fully return-aware route needs a separate
head-return/return-profile assembly theorem.
-/

/-- Current-environment block-body summary. -/
structure BlockBodySummaryAt (Γ : TypeEnv) (ss : StmtBlock) : Type where
  normalOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .normalK Γ ss Δ}
  returnOut :
    Option {Δ : TypeEnv // HasTypeBlockCI .returnK Γ ss Δ}

/-- Current-environment block-body control profile. -/
structure BlockBodyControlProfileAt (Γ : TypeEnv) (ss : StmtBlock) : Type where
  summary : BlockBodySummaryAt Γ ss

/-- Current-environment block-body entry witness. -/
inductive BlockBodyEntryWitnessAt (Γ : TypeEnv) (ss : StmtBlock) : Type where
  | normal :
      {Δ : TypeEnv // HasTypeBlockCI .normalK Γ ss Δ} →
      BlockBodyEntryWitnessAt Γ ss
  | returned :
      {Δ : TypeEnv // HasTypeBlockCI .returnK Γ ss Δ} →
      BlockBodyEntryWitnessAt Γ ss

/-- Entry/profile coherence for current-environment block-body profiles. -/
inductive BlockBodyRootCoherentAt
    {Γ : TypeEnv} {ss : StmtBlock}
    (profile : BlockBodyControlProfileAt Γ ss) :
    BlockBodyEntryWitnessAt Γ ss → Prop where
  | normal {out} :
      profile.summary.normalOut = some out →
      BlockBodyRootCoherentAt profile (.normal out)
  | returned {out} :
      profile.summary.returnOut = some out →
      BlockBodyRootCoherentAt profile (.returned out)

/--
Current-environment opened block-body contract with CI profile.

This is the recursion-friendly form that should replace the old-typing
`BlockBodyReadyConcreteAt` route once upstream callers can supply enough CI
profile payloads.  The current theorem-backed driver below uses the normal
channel explicitly; the return-only route is deliberately not faked here.
-/
structure BlockBodyReadyConcreteAtCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  wf : WellFormedBlock ss
  profile : BlockBodyControlProfileAt Γ ss
  root : BlockBodyEntryWitnessAt Γ ss
  rootCoherent : BlockBodyRootCoherentAt profile root
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

/-- Extract the head statement boundary from a CI current-env cons block body using
an explicit normal block-body payload. -/
def blockBodyReadyConcreteAtCI_cons_head_of_normalOut
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ}) :
    BodyReadyConcrete Γ σ s := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using h.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using h.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using h.continueScoped
  have htypedHead : WellTypedFrom Γ s := by
    rcases out with ⟨Ω, htyBlock⟩
    cases htyBlock with
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

/--
Reconstruct the CI current-env tail boundary after a normal head execution.

The returned tail profile is intentionally conservative:
- its normal channel is obtained from the normal `cons` payload;
- its return channel is set to `none`.

Projecting the return channel honestly would require a head-normal post
environment uniqueness theorem to align the head environment used by the whole
return payload with the one obtained from the chosen normal payload.  We do not
invent that equality here.
-/
theorem blockBodyReadyConcreteAtCI_cons_tail_after_head_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hstep : BigStepStmt σ s .normal σ') :
    ∃ Δ, ∃ htail : BlockBodyReadyConcreteAtCI Δ σ' ss,
      ∃ outTail, htail.profile.summary.normalOut = some outTail := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using h.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using h.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using h.continueScoped
  rcases out with ⟨Ω, htyBlock⟩
  cases htyBlock with
  | cons_normal htyHead htyTail =>
      rename_i Θ
      rcases cons_block_ready_tail_after_head_normal_ci
          mkWhileReentry htyHead h.state h.safe hstep with
        ⟨hstate', hreadyTail⟩
      let outTail : {Δ : TypeEnv // HasTypeBlockCI .normalK Θ ss Δ} :=
        ⟨Ω, htyTail⟩
      let profileTail : BlockBodyControlProfileAt Θ ss :=
        { summary :=
            { normalOut := some outTail
              returnOut := none } }
      let htail : BlockBodyReadyConcreteAtCI Θ σ' ss :=
        { wf := hwf.2
          profile := profileTail
          root := .normal outTail
          rootCoherent := by
            exact BlockBodyRootCoherentAt.normal rfl
          breakScoped := hbreak.2
          continueScoped := hcont.2
          state := hstate'
          safe := hreadyTail }
      exact ⟨Θ, htail, outTail, rfl⟩

/-- `nil` opened block body closes immediately with fallthrough in the CI route. -/
theorem nil_block_body_function_closure_concrete_refined_at_ci
    {Γ : TypeEnv} {σ : State}
    (_h : BlockBodyReadyConcreteAtCI Γ σ .nil) :
    (∃ ex σ', BigStepFunctionBlockBody σ .nil ex σ') ∨ BigStepBlockDiv σ .nil := by
  left
  refine ⟨.fellThrough, σ, ?_⟩
  exact BigStepFunctionBlockBody.fallthrough BigStepBlock.nil

/-- Head/tail closure callback for a normal head execution in the CI current-env route. -/
private theorem blockBodyReadyConcreteAtCI_tailClosure_after_head_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (htail :
      ∀ {Δ : TypeEnv} {σ' : State}
        (htailReady : BlockBodyReadyConcreteAtCI Δ σ' ss),
        (∃ out, htailReady.profile.summary.normalOut = some out) →
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss)
    {σ' : State}
    (hstep : BigStepStmt σ s .normal σ') :
    (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss := by
  rcases blockBodyReadyConcreteAtCI_cons_tail_after_head_normal
      mkWhileReentry h out hstep with
    ⟨Δ, htailReady, htailN⟩
  exact htail htailReady htailN

/-- Head/tail assembly for a `cons` opened block body in the CI current-env route,
under an explicit normal-channel assumption. -/
theorem cons_block_body_function_closure_concrete_refined_at_ci
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (h : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (hN : ∃ out, h.profile.summary.normalOut = some out)
    (htail :
      ∀ {Δ : TypeEnv} {σ' : State}
        (htailReady : BlockBodyReadyConcreteAtCI Δ σ' ss),
        (∃ out, htailReady.profile.summary.normalOut = some out) →
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons s ss) ex σ') ∨
      BigStepBlockDiv σ (.cons s ss) := by
  rcases hN with ⟨out, _hout⟩
  have hheadReady : BodyReadyConcrete Γ σ s :=
    blockBodyReadyConcreteAtCI_cons_head_of_normalOut h out
  -- ↓ ここからがパッチ適用後の新しいコード
  have hheadClosure :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s :=
    concrete_body_ready_function_body_progress_or_diverges_by_cases_concrete_refined
      (coreBigStepFragment_all s)
      hheadReady
  exact
    block_cons_function_body_result_return_aware
      hheadClosure
      (blockBodyReadyConcreteAtCI_tailClosure_after_head_normal
        mkWhileReentry h out htail)

/--
Opened block-body closure in the CI current-env concrete route, for profiles
whose normal channel is present.

This theorem is deliberately not named as the full profile-aware closure theorem:
return-only profiles require a separate return-aware driver.
-/
theorem block_body_function_closure_concrete_refined_at_ci
    (mkWhileReentry : WhileReentryReadyProvider) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
      (h : BlockBodyReadyConcreteAtCI Γ σ ss),
      (∃ out, h.profile.summary.normalOut = some out) →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss
  | _, _, .nil, h, _hN =>
      nil_block_body_function_closure_concrete_refined_at_ci h
  | _, _, .cons _ _, h, hN =>
      cons_block_body_function_closure_concrete_refined_at_ci mkWhileReentry h hN
        (fun htail htailN =>
          block_body_function_closure_concrete_refined_at_ci
            mkWhileReentry htail htailN)

end Cpp
