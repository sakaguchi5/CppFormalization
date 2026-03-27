import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete

namespace Cpp

/-!
# Closure.Internal.BlockBodyClosureCI

CI-centric opened block-body closure layer.

役割:
- `BodyReadyCI` から opened scope の下の `BlockBodyReadyCI` へ移る honest boundary を置く。
- block statement と block body を分離したまま、function-body closure の block 節を支える。
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

/-- Honest opened-scope bridge into the CI block-body boundary.

This is the one place where old typing still enters from the top-level body boundary;
all control-sensitive work below this point is expected to be carried by CI witnesses.
-/
axiom blockBodyReadyCI_of_bodyReadyCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyReadyCI Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockBodyReadyCI Γ σ' ss

/-- CI-boundary block-body closure target. -/
axiom block_body_function_closure_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyReadyCI Γ σ ss →
    (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss

/-- Honest block-statement closure assembled from opened block-body closure. -/
axiom block_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyReadyCI Γ σ (.block ss) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨ BigStepStmtDiv σ (.block ss)

end Cpp
