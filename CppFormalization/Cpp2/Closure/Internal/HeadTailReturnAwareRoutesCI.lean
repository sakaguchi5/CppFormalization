import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcrete
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.HeadTailReturnAwareRoutesCI

Return-aware operational assembly for `seq` and block-body `cons`.

This file is deliberately low-level. It imports only the concrete block-body
execution wrapper and divergence semantics, so it can be used by
`BlockBodyClosureConcreteCI` without creating an import cycle.
-/

/-- Return-aware assembly for statement sequencing. -/
theorem seq_function_body_result_return_aware
    {σ : State} {s t : CppStmt}
    (hhead :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (tailAfterHeadNormal :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨
          BigStepStmtDiv σ' t) :
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨
      BigStepStmtDiv σ (.seq s t) := by
  rcases hhead with hheadTerm | hheadDiv
  · rcases hheadTerm with ⟨exHead, σ1, hheadExec⟩
    cases hheadExec with
    | fallthrough hstepHead =>
        rcases tailAfterHeadNormal hstepHead with htailTerm | htailDiv
        · rcases htailTerm with ⟨exTail, σ2, htailExec⟩
          cases htailExec with
          | fallthrough hstepTail =>
              left
              refine ⟨.fellThrough, σ2, ?_⟩
              exact BigStepFunctionBody.fallthrough
                (BigStepStmt.seqNormal hstepHead hstepTail)
          | returning hstepTail =>
              rename_i rv
              left
              exact
                ⟨.returned rv, σ2,
                  BigStepFunctionBody.returning
                    (BigStepStmt.seqNormal hstepHead hstepTail)⟩
        · right
          exact BigStepStmtDiv.seqRight hstepHead htailDiv
    | returning hstepHead =>
        rename_i rv
        left
        exact
          ⟨.returned rv, σ1,
            BigStepFunctionBody.returning
              (BigStepStmt.seqReturn hstepHead)⟩
  · right
    exact BigStepStmtDiv.seqLeft hheadDiv

/-- Return-aware assembly for block-body cons. -/
theorem block_cons_function_body_result_return_aware
    {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hhead :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (tailAfterHeadNormal :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨
          BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons s ss) ex σ') ∨
      BigStepBlockDiv σ (.cons s ss) := by
  rcases hhead with hheadTerm | hheadDiv
  · rcases hheadTerm with ⟨exHead, σ1, hheadExec⟩
    cases hheadExec with
    | fallthrough hstepHead =>
        rcases tailAfterHeadNormal hstepHead with htailTerm | htailDiv
        · rcases htailTerm with ⟨exTail, σ2, htailExec⟩
          cases htailExec with
          | fallthrough hstepTail =>
              left
              refine ⟨.fellThrough, σ2, ?_⟩
              exact BigStepFunctionBlockBody.fallthrough
                (BigStepBlock.consNormal hstepHead hstepTail)
          | returning hstepTail =>
              rename_i rv
              left
              exact
                ⟨.returned rv, σ2,
                  BigStepFunctionBlockBody.returning
                    (BigStepBlock.consNormal hstepHead hstepTail)⟩
        · right
          exact BigStepBlockDiv.consTail hstepHead htailDiv
    | returning hstepHead =>
        rename_i rv
        left
        exact
          ⟨.returned rv, σ1,
            BigStepFunctionBlockBody.returning
              (BigStepBlock.consReturn hstepHead)⟩
  · right
    exact BigStepBlockDiv.consHere hheadDiv

end Cpp
