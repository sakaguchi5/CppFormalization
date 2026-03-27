import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureCI

namespace Cpp

/-!
# Closure.Internal.InternalClosureRoadmapCI

CI-centric internal closure roadmap.

目的:
- theorem-backed concrete kernel をそのまま流用しつつ、
  function-body closure の入口を old `BodyReady` から `BodyReadyCI` へ移す。
- old abstract roadmap は coarse external facade として残し、
  internal closure 主線はこちらを使う。
-/

namespace InternalClosureRoadmapCI

/-! ## theorem-backed concrete normal kernel re-exported through the CI roadmap -/

theorem stmt_normal_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {st : CppStmt}
    (hty : HasTypeStmtCI .normalK Γ st Δ)
    (hready : StmtReadyConcrete Γ σ st)
    (hstep : BigStepStmt σ st .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ' :=
  Cpp.stmt_normal_preserves_scoped_typed_state_concrete hty hσ hready hstep

theorem block_body_normal_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .normalK Γ ss Δ)
    (hready : BlockReadyConcrete Γ σ ss)
    (hstep : BigStepBlock σ ss .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ' :=
  Cpp.block_body_normal_preserves_scoped_typed_state_concrete hty hσ hready hstep

theorem seq_left_normal_preserves_stmt_ready
    {Γ Δ : TypeEnv} {σ σ' : State} {s t : CppStmt}
    (htyS : HasTypeStmtCI .normalK Γ s Δ)
    (hready : StmtReadyConcrete Γ σ (.seq s t))
    (hstepS : BigStepStmt σ s .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    StmtReadyConcrete Δ σ' t :=
  InternalClosureRoadmapConcrete.seq_left_normal_preserves_body_ready htyS hready hstepS hσ

theorem block_head_normal_preserves_block_ready
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (htyS : HasTypeStmtCI .normalK Γ s Δ)
    (hready : BlockReadyConcrete Γ σ (.cons s ss))
    (hstepS : BigStepStmt σ s .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    BlockReadyConcrete Δ σ' ss :=
  InternalClosureRoadmapConcrete.block_head_normal_preserves_block_ready htyS hready hstepS hσ

theorem while_body_normal_preserves_stmt_ready_typed
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hready : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hstepBody : BigStepStmt σ body .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  InternalClosureRoadmapConcrete.while_body_normal_preserves_body_ready_typed htyWhile hready hstepBody hσ

theorem while_body_continue_preserves_stmt_ready_typed
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hready : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hstepBody : BigStepStmt σ body .continueResult σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  InternalClosureRoadmapConcrete.while_body_continue_preserves_body_ready_typed htyWhile hready hstepBody hσ

/-! ## CI-boundary function-body closure -/

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
    | fellThrough =>
        refine ⟨.normal, σ', ?_⟩
        simpa using (BigStepFunctionBody.to_stmt hfb)
    | returned rv =>
        refine ⟨.returnResult rv, σ', ?_⟩
        simpa using (BigStepFunctionBody.to_stmt hfb)
  · exact Or.inr hdiv

end InternalClosureRoadmapCI

end Cpp
