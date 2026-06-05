import CppFormalization.Cpp2.Entry.Body.BlockBodyReadyAtCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureCI

namespace Cpp

/-!
# Closure.Internal.BlockBodyReadyAtCIClosure

Provider-explicit CI-native opened block-body closure.

This file advances the old-typing removal route without editing the legacy
concrete `BlockBodyReadyConcreteAt` path.  It makes three debts explicit:

* statement closure from `BodyReadyAtCI`;
* conversion from assembled opened block-body boundary to `BlockBodyReadyAtCI`;
* cons-tail reconstruction after a normal head execution.
-/

/--
Provider that upgrades a `BodyReadyAtCI` entry into the assembled statement
closure boundary expected by the existing CI closure roots.
-/
abbrev BodyReadyAtCIClosureBoundaryProvider : Type :=
  ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
    BodyReadyAtCI Γ σ st →
    BodyClosureBoundaryCI Γ σ st

namespace BodyReadyAtCIClosureProvider

/--
Connect `BodyReadyAtCI` statement closure to the existing `BodyClosureBoundaryCI`
root.
-/
def ofBodyClosureBoundaryCI
    (mkBoundary : BodyReadyAtCIClosureBoundaryProvider) :
    BodyReadyAtCIClosureProvider := by
  intro Γ σ st hfrag hready
  exact
    body_closure_ci_function_body_progress_or_diverges
      hfrag
      (mkBoundary hready)

/--
Connect `BodyReadyAtCI` statement closure to the explicit mainline continuation
root.
-/
def ofMainlineContinuation
    (Primitive : FunctionBodyPrimitiveClosureSupportCI)
    (Ite : FunctionBodyIteClosureSupportCI)
    (P : StmtNormalPreservationCoreCI)
    (SeqSlots : FunctionBodySeqSlotSelectionDataSupportCI)
    (Seq : SeqFunctionBodyClosureContinuationDataSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (Block : FunctionBodyBlockClosureSupportCI)
    (IH : FunctionBodyContinuationCaseDriverIH)
    (mkBoundary : BodyReadyAtCIClosureBoundaryProvider) :
    BodyReadyAtCIClosureProvider := by
  intro Γ σ st hfrag hready
  exact
    body_closure_ci_function_body_progress_or_diverges_mainline_continuation
      Primitive
      Ite
      P
      SeqSlots
      Seq
      Wh
      W
      Block
      IH
      hfrag
      (mkBoundary hready)

end BodyReadyAtCIClosureProvider

/-
Head/tail assembly for a `cons` opened block body in the CI-native current-env
layer, with statement closure supplied explicitly.
-/

/-!
## Source closure / successor / recursion-shell split

For the CI-native opened block-body closure, the cons case is read as follows.

* `bodyClosure` closes the source head statement.
* `successor` is the C++ block-cons normal successor edge:
  if the head falls through normally, reconstruct the tail boundary under the
  post-head environment and state.
* `htail` is the recursive closure shell for the reconstructed tail boundary.

The successor is the semantic C++ control-flow fact.  The recursive tail closure
is proof architecture.
-/

theorem cons_block_body_function_closure_ci_at_with_statement_provider
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

/--
CI-native opened block-body closure with statement closure supplied explicitly.
-/
theorem block_body_function_closure_ci_at_with_statement_provider
    (bodyClosure : BodyReadyAtCIClosureProvider)
    (successor : ControlSuccessor.BlockConsNormalSuccessorProvider) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock},
      BlockBodyReadyAtCI Γ σ ss →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss
  | _, _, .nil, _ =>
      nil_block_body_function_closure_at
  | _, _, .cons _ _, h =>
      cons_block_body_function_closure_ci_at_with_statement_provider
        bodyClosure
        successor
        h
        (fun htail =>
          block_body_function_closure_ci_at_with_statement_provider
            bodyClosure
            successor
            htail)

/--
Opened block-body closure from assembled CI boundary, with all remaining
providers explicit.

This is the replacement surface for the earlier monolithic
`blockBodyReadyAtCI_of_blockBodyClosureBoundaryCI` axiom.
-/
theorem block_body_function_closure_boundary_ci_with_providers
    (bodyClosure : BodyReadyAtCIClosureProvider)
    (successor : ControlSuccessor.BlockConsNormalSuccessorProvider)
    (headProvider : BlockBodyReadyAtCIHeadProvider)
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss →
    (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss := by
  intro hentry
  exact
    block_body_function_closure_ci_at_with_statement_provider
      bodyClosure
      successor
      (blockBodyReadyAtCI_of_blockBodyClosureBoundaryCI_withHeadProvider
        headProvider
        hentry)

end Cpp
