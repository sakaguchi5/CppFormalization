
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureCI

namespace Cpp

namespace InternalClosureRoadmapCI

theorem stmt_normal_preserves_scoped_typed_state
    (mkWhileCtx : WhileCtxProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt}
    (hty : HasTypeStmtCI .normalK Γ st Δ)
    (hready : StmtReadyConcrete Γ σ st)
    (hstep : BigStepStmt σ st .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ' :=
  Cpp.stmt_normal_preserves_scoped_typed_state_concrete mkWhileCtx hty hσ hready hstep

theorem block_body_normal_preserves_scoped_typed_state
    (mkWhileCtx : WhileCtxProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .normalK Γ ss Δ)
    (hready : BlockReadyConcrete Γ σ ss)
    (hstep : BigStepBlock σ ss .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ' :=
  Cpp.block_body_normal_preserves_scoped_typed_state_concrete mkWhileCtx hty hσ hready hstep

theorem seq_left_normal_preserves_stmt_ready
    (mkWhileCtx : WhileCtxProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (htyS : HasTypeStmtCI .normalK Γ s Δ)
    (hready : StmtReadyConcrete Γ σ (.seq s t))
    (hstepS : BigStepStmt σ s .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    StmtReadyConcrete Δ σ' t :=
  InternalClosureRoadmapConcrete.seq_left_normal_preserves_body_ready mkWhileCtx htyS hready hstepS hσ

theorem block_head_normal_preserves_block_ready
    (mkWhileCtx : WhileCtxProvider)
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (htyS : HasTypeStmtCI .normalK Γ s Δ)
    (hready : BlockReadyConcrete Γ σ (.cons s ss))
    (hstepS : BigStepStmt σ s .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    BlockReadyConcrete Δ σ' ss :=
  InternalClosureRoadmapConcrete.block_head_normal_preserves_block_ready mkWhileCtx htyS hready hstepS hσ

theorem while_body_normal_preserves_stmt_ready_typed
    (mkWhileCtx : WhileCtxProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  InternalClosureRoadmapConcrete.while_body_normal_preserves_body_ready_typed
    mkWhileCtx hcond hbody K hstepBody

theorem while_body_continue_preserves_stmt_ready_typed
    (mkWhileCtx : WhileCtxProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  InternalClosureRoadmapConcrete.while_body_continue_preserves_body_ready_typed
    mkWhileCtx hcond hbody K hstepBody

theorem body_ready_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  exact Cpp.body_ready_ci_function_body_progress_or_diverges hfrag hready

theorem body_ready_ci_stmt_terminates_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  rcases body_ready_ci_function_body_progress_or_diverges hfrag hready with hbody | hdiv
  · left
    rcases hbody with ⟨ex, σ', hfb⟩
    cases ex with
    | fellThrough => refine ⟨.normal, σ', by simpa using (BigStepFunctionBody.to_stmt hfb)⟩
    | returned rv => refine ⟨.returnResult rv, σ', by simpa using (BigStepFunctionBody.to_stmt hfb)⟩
  · exact Or.inr hdiv

theorem body_closure_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hboundary
  exact Cpp.body_closure_ci_function_body_progress_or_diverges hfrag hboundary

theorem body_closure_stmt_terminates_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyClosureBoundaryCI Γ σ st →
    BigStepStmtTerminates σ st ∨ BigStepStmtDiv σ st := by
  intro hfrag hboundary
  rcases body_closure_function_body_progress_or_diverges hfrag hboundary with hbody | hdiv
  · left
    rcases hbody with ⟨ex, σ', hfb⟩
    cases ex with
    | fellThrough => refine ⟨.normal, σ', by simpa using (BigStepFunctionBody.to_stmt hfb)⟩
    | returned rv => refine ⟨.returnResult rv, σ', by simpa using (BigStepFunctionBody.to_stmt hfb)⟩
  · exact Or.inr hdiv

end InternalClosureRoadmapCI

end Cpp
