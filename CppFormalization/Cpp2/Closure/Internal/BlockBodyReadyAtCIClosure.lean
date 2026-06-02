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
Statement closure provider for `BodyReadyAtCI`.

This is the old-free replacement surface for the temporary
`body_ready_at_ci_function_body_progress_or_diverges` shell.
-/
abbrev BodyReadyAtCIClosureProvider : Prop :=
  ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
    CoreBigStepFragment st →
    BodyReadyAtCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

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

/--
Head/tail assembly for a `cons` opened block body in the CI-native current-env
layer, with statement closure supplied explicitly.
-/
theorem cons_block_body_function_closure_ci_at_with_statement_provider
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
    (bodyClosure : BodyReadyAtCIClosureProvider)
    (tailAfterHead : BlockBodyReadyAtCITailAfterHeadProvider)
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
          tailAfterHead h hheadCI hstepHead

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
    (tailAfterHead : BlockBodyReadyAtCITailAfterHeadProvider) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock},
      BlockBodyReadyAtCI Γ σ ss →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss
  | _, _, .nil, _ =>
      nil_block_body_function_closure_concrete_refined_at
  | _, _, .cons _ _, h =>
      cons_block_body_function_closure_ci_at_with_statement_provider
        bodyClosure
        tailAfterHead
        h
        (fun htail =>
          block_body_function_closure_ci_at_with_statement_provider
            bodyClosure
            tailAfterHead
            htail)

/--
Opened block-body closure from assembled CI boundary, with all remaining
providers explicit.

This is the replacement surface for the earlier monolithic
`blockBodyReadyAtCI_of_blockBodyClosureBoundaryCI` axiom.
-/
theorem block_body_function_closure_boundary_ci_with_providers
    (bodyClosure : BodyReadyAtCIClosureProvider)
    (tailAfterHead : BlockBodyReadyAtCITailAfterHeadProvider)
    (headProvider : BlockBodyReadyAtCIHeadProvider)
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BlockBodyClosureBoundaryCI Γ σ ss →
    (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨ BigStepBlockDiv σ ss := by
  intro hentry
  exact
    block_body_function_closure_ci_at_with_statement_provider
      bodyClosure
      tailAfterHead
      (blockBodyReadyAtCI_of_blockBodyClosureBoundaryCI_withHeadProvider
        headProvider
        hentry)

end Cpp
