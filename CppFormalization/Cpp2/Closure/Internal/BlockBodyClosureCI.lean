import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete
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
Honest opened-scope bridge into the assembled CI block-body boundary.

重要:
- これは top-level `.block ss` entry から opened body `ss` へ移る唯一の shell surface.
- block statement と opened block body を混同しないため、
  target は `BodyClosureBoundaryCI` ではなく `BlockBodyClosureBoundaryCI` にする。
-/
axiom blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockBodyClosureBoundaryCI Γ σ' ss

/--
Opened block-body closure target.

ここでは result wrapper も block-body 専用に保つ。
top-level statement `.block ss` への再包装は別 theorem で行う。
-/
axiom block_body_function_closure_boundary_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss →
    FunctionBlockBodyClosureResult σ ss

/--
Honest block-statement closure assembled from opened block-body closure.

必要なものを明示する:
- current entry boundary for `.block ss`
- opened state `σ0` での opened-scope witness
- opened block body の assembled boundary
- その境界の下での opened block-body closure
-/
axiom block_function_body_closure_boundary_ci_from_opened_body
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (hentry : BodyClosureBoundaryCI Γ σ (.block ss))
    (openedClosure :
      ∀ {σ0 : State},
        OpenScope σ σ0 →
        BlockBodyClosureBoundaryCI Γ σ0 ss →
        FunctionBlockBodyClosureResult σ0 ss) :
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss)

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
