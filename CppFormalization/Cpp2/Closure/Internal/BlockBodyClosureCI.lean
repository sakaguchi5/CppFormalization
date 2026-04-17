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

theorem blockBodyReadyConcrete_of_blockBodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss → BlockBodyReadyConcrete Γ σ ss := by
  intro h
  exact blockBodyReadyConcrete_of_blockBodyReadyCI h.toBlockBodyReadyCI

abbrev FunctionBlockBodyClosureResult (σ : State) (ss : StmtBlock) : Prop :=
  (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss

structure BlockOpenedClosureScaffoldCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  structural : BlockBodyStructuralBoundary Γ ss
  profile : BlockBodyControlProfile Γ ss
  adequacy : BlockBodyAdequacyCI Γ σ ss profile

axiom blockBodyClosureScaffoldCI_of_bodyClosureBoundaryCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockOpenedClosureScaffoldCI Γ σ' ss

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

noncomputable def blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockBodyClosureBoundaryCI Γ σ' ss := by
  intro hentry hopen
  let hs := blockBodyClosureScaffoldCI_of_bodyClosureBoundaryCI_opened hentry hopen
  let hd := blockBodyDynamicBoundary_of_bodyClosureBoundaryCI_opened hentry hopen
  exact mkBlockBodyClosureBoundaryCI hs.structural hs.profile hd hs.adequacy

theorem block_body_function_closure_boundary_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss →
    FunctionBlockBodyClosureResult σ ss := by
  intro hentry
  exact
    block_body_function_closure_concrete_refined
      (blockBodyReadyConcrete_of_blockBodyClosureBoundaryCI hentry)

theorem block_function_body_closure_boundary_ci_direct
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyClosureBoundaryCI Γ σ (.block ss) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨
      BigStepStmtDiv σ (.block ss) := by
  intro hentry
  exact
    block_function_body_closure_concrete_refined_honest
      (bodyReadyConcrete_of_bodyClosureBoundaryCI hentry)

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

noncomputable def blockBodyReadyCI_of_bodyReadyCI_opened
    {Γ : TypeEnv} {σ σ' : State} {ss : StmtBlock} :
    BodyReadyCI Γ σ (.block ss) →
    OpenScope σ σ' →
    BlockBodyReadyCI Γ σ' ss := by
  intro hentry hopen
  exact
    (blockBodyClosureBoundaryCI_of_bodyClosureBoundaryCI_opened
      hentry.toClosureBoundary hopen).toBlockBodyReadyCI

theorem block_body_function_closure_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyReadyCI Γ σ ss →
    FunctionBlockBodyClosureResult σ ss := by
  intro hentry
  exact block_body_function_closure_boundary_ci hentry.toClosureBoundary

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
