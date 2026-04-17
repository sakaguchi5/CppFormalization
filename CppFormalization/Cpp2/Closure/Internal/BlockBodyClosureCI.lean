import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyPrimitiveClosureCI
import CppFormalization.Cpp2.Closure.Transitions.Minor.OpenScopeDecomposition
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.BlockBodyClosureCI

CI-centric opened block-body closure layer.

役割:
- `BodyReadyCI` / `BodyClosureBoundaryCI` から opened scope の下の
  `BlockBodyReadyCI` / `BlockBodyClosureBoundaryCI` へ移る honest boundary を置く。
- block statement と block body を分離したまま、
  function-body closure の block 節を支える。
- `FunctionBodyCaseSplitCI` から block 固有 shell を外し、
  opened block-body 専用 surface をこのファイルへ集約する。

更新:
- block-body closure と top-level block closure 自体は、
  既存の concrete refined theorem を経由して theorem-backed にした。
- opened block-body boundary bridge についても dynamic / structural に加えて
  profile まで theorem-backed にした。
- 残る shell は opened block body adequacy だけである。
-/

/-- Forget CI-sensitive block-body fields and recover the existing concrete boundary. -/
theorem blockBodyReadyConcrete_of_blockBodyReadyCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyReadyCI Γ σ ss → BlockBodyReadyConcrete Γ σ ss := by
  intro h
  exact {
    wf := h.wf
    typed := h.typed0
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped
    state := h.state
    safe := h.safe
  }

/-- Forgetful map from assembled opened block-body boundary to the refined concrete one. -/
theorem blockBodyReadyConcrete_of_blockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss → BlockBodyReadyConcrete Γ σ ss := by
  intro h
  exact blockBodyReadyConcrete_of_blockBodyReadyCI h.toBlockBodyReadyCI

/-- canonical result shape for opened block-body closure. -/
abbrev FunctionBlockBodyClosureResult (σ : State) (ss : StmtBlock) : Prop :=
  (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss

/--
The only remaining shell payload for the opened block-body bridge.

重要:
- structural / profile / dynamic は theorem-backed に復元できる。
- 残る open obligation は adequacy だけである。
-/
structure BlockOpenedAdequacyScaffoldCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfile Γ ss) : Type where
  adequacy : BlockBodyAdequacyCI Γ σ ss P

/--
Theorem-backed structural projection from a top-level block entry to the opened block body.
-/
theorem blockBodyStructuralBoundary_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    BlockBodyStructuralBoundary Γ ss := by
  intro hentry
  refine
    { wf := by
        simpa [WellFormedStmt] using hentry.structural.wf
      typed0 := by
        rcases hentry.structural.typed0 with ⟨Δ, hty⟩
        cases hty with
        | block hB =>
            exact ⟨_, hB⟩
      breakScoped := by
        simpa [BreakWellScoped, BreakWellScopedAt] using hentry.structural.breakScoped
      continueScoped := by
        simpa [ContinueWellScoped, ContinueWellScopedAt] using hentry.structural.continueScoped }

theorem block_normal_payload_exists_ci
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    (h : HasTypeStmtCI .normalK Γ (.block ss) Δ) :
    ∃ Θ, HasTypeBlockCI .normalK (pushTypeScope Γ) ss Θ := by
  cases h with
  | block hB =>
      exact ⟨_, hB⟩

theorem block_return_payload_exists_ci
    {Γ Δ : TypeEnv} {ss : StmtBlock}
    (h : HasTypeStmtCI .returnK Γ (.block ss) Δ) :
    ∃ Θ, HasTypeBlockCI .returnK (pushTypeScope Γ) ss Θ := by
  cases h with
  | block hB =>
      exact ⟨_, hB⟩



/--
Project a statement-body summary for `.block ss` to the corresponding opened block-body summary.

重要:
- `.block ss` の statement summary は payload の中に opened block body typing を持っている。
- したがって profile 自体は theorem-backed に recover できる。
- recover できないのは actual opened-body execution に対する adequacy の方である。
-/
noncomputable def blockBodySummary_of_stmtBodySummary
    {Γ : TypeEnv} {ss : StmtBlock} :
    StmtBodySummary Γ (.block ss) →
    BlockBodySummary Γ ss
  | { normalOut := n, returnOut := r } =>
      { normalOut :=
          match n with
          | none => none
          | some ⟨_, hty⟩ =>
              let hex : ∃ Θ, HasTypeBlockCI .normalK (pushTypeScope Γ) ss Θ :=
                block_normal_payload_exists_ci hty
              some ⟨Classical.choose hex, Classical.choose_spec hex⟩
        returnOut :=
          match r with
          | none => none
          | some ⟨_, hty⟩ =>
              let hex : ∃ Θ, HasTypeBlockCI .returnK (pushTypeScope Γ) ss Θ :=
                block_return_payload_exists_ci hty
              some ⟨Classical.choose hex, Classical.choose_spec hex⟩ }

/--
Theorem-backed profile projection from a top-level block entry to the opened block body.
-/
noncomputable def blockBodyProfile_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    BlockBodyControlProfile Γ ss
  | hentry =>
      { summary := blockBodySummary_of_stmtBodySummary hentry.profile.summary }

/--
Opened block-body adequacy scaffold projected from a top-level block entry.

重要:
- ここが block bridge に残る唯一の shell である。
- opened block body の adequacy は `.block ss` statement の top-level adequacy
  からは recover できないため、still-open obligation として残す。
-/
axiom blockBodyAdequacyScaffoldCI_of_bodyClosureBoundaryCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (hopen : OpenScope σ σ') :
    BlockOpenedAdequacyScaffoldCI Γ σ' ss
      (blockBodyProfile_of_bodyClosureBoundaryCI hentry)

/--
Theorem-backed dynamic opened block-body boundary.

This is the dynamic part of the bridge, obtained from the concrete opened-body theorem.
-/
def blockBodyDynamicBoundary_of_bodyClosureBoundaryCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (hopen : OpenScope σ σ') :
    BlockBodyDynamicBoundary Γ σ' ss :=
  let hopened :=
    blockBodyReadyConcrete_of_bodyReadyConcrete_opened
      (bodyReadyConcrete_of_bodyClosureBoundaryCI hentry) hopen
  { state := hopened.state
    safe := hopened.safe }

/--
Opened-scope bridge into the assembled CI block-body boundary.

もはや full shell ではない。
opened body の structural / profile / dynamic は theorem-backed に再構成し、
残る adequacy だけを shell から受け取って assembled boundary を作る。
-/
noncomputable def blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockBodyClosureBoundaryCI Γ σ' ss := by
  intro hentry hopen
  let hs := blockBodyStructuralBoundary_of_bodyClosureBoundaryCI hentry
  let hp := blockBodyProfile_of_bodyClosureBoundaryCI hentry
  let ha := blockBodyAdequacyScaffoldCI_of_bodyClosureBoundaryCI_opened hentry hopen
  let hd := blockBodyDynamicBoundary_of_bodyClosureBoundaryCI_opened hentry hopen
  exact mkBlockBodyClosureBoundaryCI hs hp hd ha.adequacy

/--
Opened block-body closure target.

ここでは result wrapper も block-body 専用に保つ。
CI 層では theorem-backed だが、実質的な仕事は concrete refined theorem に委譲する。
-/
theorem block_body_function_closure_boundary_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss →
    FunctionBlockBodyClosureResult σ ss := by
  intro hentry
  exact
    block_body_function_closure_concrete_refined
      (blockBodyReadyConcrete_of_blockBodyClosureBoundaryCI hentry)

/--
Direct block-statement closure from the top-level block entry.

block statement と opened block body を理論上は分けたままにするが、
CI 層の closure theorem 自体は concrete refined の honest theorem へ落とす。
-/
theorem block_function_body_closure_boundary_ci_direct
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss) := by
  intro hentry
  exact
    block_function_body_closure_concrete_refined_honest
      (bodyReadyConcrete_of_bodyClosureBoundaryCI hentry)

/--
Block-statement closure assembled from an opened block-body closure callback.

`openedClosure` is intentionally kept in the surface for architectural honesty,
but the actual CI theorem is already discharged by the concrete refined theorem.
-/
theorem block_function_body_closure_boundary_ci_from_opened_body
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (_openedClosure :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        BlockBodyClosureBoundaryCI Γ σ0 ss →
        FunctionBlockBodyClosureResult σ0 ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss) := by
  exact block_function_body_closure_boundary_ci_direct hentry

/-- `BodyReadyCI` 互換 wrapper for the opened-scope bridge. -/
noncomputable def blockBodyReadyCI_of_bodyReadyCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyReadyCI Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockBodyReadyCI Γ σ' ss := by
  intro hentry hopen
  exact
    (blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened
      hentry.toClosureBoundary hopen).toBlockBodyReadyCI

/-- `BodyReadyCI` 互換 wrapper for opened block-body closure. -/
theorem block_body_function_closure_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyReadyCI Γ σ ss →
    FunctionBlockBodyClosureResult σ ss := by
  intro hentry
  exact block_body_function_closure_boundary_ci hentry.toClosureBoundary

/-- `BodyReadyCI` 互換 wrapper for honest block-statement closure. -/
theorem block_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hentry : BodyReadyCI Γ σ (.block ss))
    (openedClosure :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        BlockBodyReadyCI Γ σ0 ss →
        FunctionBlockBodyClosureResult σ0 ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss) := by
  exact
    block_function_body_closure_boundary_ci_from_opened_body
      hentry.toClosureBoundary
      (fun hopen hopenedBoundary =>
        openedClosure hopen hopenedBoundary.toBlockBodyReadyCI)

end Cpp
