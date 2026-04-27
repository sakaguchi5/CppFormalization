import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcreteCI
import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.HeadTailReturnAwareRoutesCI

Return-aware operational assembly for `seq` and block-body `cons`.

This file deliberately separates the operational head/tail assembly from profile
projection.  The core point is:

* head return is handled as head return;
* head normal is the only path that constructs a tail boundary and invokes the
  tail closure route;
* divergence is propagated from the actual point where it occurs.

This avoids the false move of projecting a whole-return payload into a tail
return profile.
-/

/--
Return-aware assembly for statement sequencing.

This theorem is profile-independent on purpose.  It states the semantic shape
that every honest CI/profile route must eventually feed:
- if the head returns, the whole sequence returns immediately;
- if the head falls through, the tail closure decides the whole result;
- if the head diverges, the whole sequence diverges at the head.
-/
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

/--
Return-aware assembly for block-body cons.

This is the block-body analogue of `seq_function_body_result_return_aware`.
It is the operational core that profile-aware block-body routes should call.
-/
theorem block_cons_function_body_result_return_aware
    {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hhead :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (tailAfterHeadNormal :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        FunctionBlockBodyClosureResult σ' ss) :
    FunctionBlockBodyClosureResult σ (.cons s ss) := by
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

/--
Callback-shaped CI route for statement sequencing.

This is intentionally not a full replacement for existing seq closure yet.
It is the correct return-aware surface: the caller supplies a real head closure
and a tail closure only for the actual head-normal execution.
-/
theorem seq_function_body_closure_boundary_ci_return_aware_from_callbacks
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (headClosure :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (tailAfterHeadNormal :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨
          BigStepStmtDiv σ' t) :
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨
      BigStepStmtDiv σ (.seq s t) := by
  exact seq_function_body_result_return_aware headClosure tailAfterHeadNormal

/--
Callback-shaped CI route for block-body cons.

This theorem is the block-side surface corresponding to the seq route above.
It should replace ad-hoc cons assembly inside profile-aware block closure code.
-/
theorem block_cons_function_body_closure_boundary_ci_return_aware_from_callbacks
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (_hentry : BlockBodyReadyConcreteAtCI Γ σ (.cons s ss))
    (headClosure :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨
        BigStepStmtDiv σ s)
    (tailAfterHeadNormal :
      ∀ {σ' : State},
        BigStepStmt σ s .normal σ' →
        FunctionBlockBodyClosureResult σ' ss) :
    FunctionBlockBodyClosureResult σ (.cons s ss) := by
  exact block_cons_function_body_result_return_aware
    headClosure tailAfterHeadNormal

end Cpp
