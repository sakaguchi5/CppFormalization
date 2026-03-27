import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureConcreteRefined
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Boundary.FunctionBody

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureCI

CI-centric function-body closure layer.

目的:
- old `BodyReady` を主線から降格し、internal closure の driver を `BodyReadyCI` に移す。
- 既存 concrete kernel (`StmtControlPreservation`, `ReadinessBoundaryConcrete`,
  `InternalClosureRoadmapConcrete`) はそのまま利用する。
- まだ theorem-backed でない function-body case split は、ここでは honest な
  CI-boundary obligation として切り出す。
-/

/-- Forget the CI-sensitive fields and recover the existing refined concrete boundary. -/
theorem bodyReadyConcrete_of_bodyReadyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    BodyReadyCI Γ σ st → BodyReadyConcrete Γ σ st := by
  intro h
  exact {
    wf := h.wf
    typed := h.typed0
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped
    state := h.state
    safe := h.safe
  }

/-- Primitive case already follows from the refined concrete layer once we forget CI extras. -/
theorem primitive_stmt_function_body_step_or_diverges_ci
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmtConcrete st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hprim hready
  exact primitive_stmt_function_body_step_or_diverges_concrete_refined hprim (bodyReadyConcrete_of_bodyReadyCI hready)

/-- Sequence closure at a CI boundary. -/
axiom seq_function_body_closure_ci
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    BodyReadyCI Γ σ (.seq s t) →
    (∀ {σ'},
      BigStepStmt σ s .normal σ' →
      BodyReadyCI Γ σ' t →
      (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨ BigStepStmtDiv σ' t) →
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨ BigStepStmtDiv σ (.seq s t)

/-- Conditional closure at a CI boundary. -/
axiom ite_function_body_closure_ci
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    BodyReadyCI Γ σ (.ite c s t) →
    (BodyReadyCI Γ σ s → (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s) →
    (BodyReadyCI Γ σ t → (∃ ex σ', BigStepFunctionBody σ t ex σ') ∨ BigStepStmtDiv σ t) →
    (∃ ex σ', BigStepFunctionBody σ (.ite c s t) ex σ') ∨ BigStepStmtDiv σ (.ite c s t)

/-- Block closure at a CI boundary. The honest opened-body formulation lives in
`BlockBodyClosureCI`; this theorem is the statement-level wrapper. -/
axiom block_function_body_closure_ci
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyReadyCI Γ σ (.block ss) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨ BigStepStmtDiv σ (.block ss)

/-- While closure at a CI boundary. -/
axiom while_function_body_closure_ci
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyReadyCI Γ σ (.whileStmt c body) →
    (∀ {σ'},
      BigStepStmt σ body .normal σ' →
      BodyReadyCI Γ σ' (.whileStmt c body) →
      (∃ ex σ'', BigStepFunctionBody σ' (.whileStmt c body) ex σ'') ∨ BigStepStmtDiv σ' (.whileStmt c body)) →
    (∀ {σ'},
      BigStepStmt σ body .continueResult σ' →
      BodyReadyCI Γ σ' (.whileStmt c body) →
      (∃ ex σ'', BigStepFunctionBody σ' (.whileStmt c body) ex σ'') ∨ BigStepStmtDiv σ' (.whileStmt c body)) →
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨ BigStepStmtDiv σ (.whileStmt c body)

/-- CI-boundary master theorem target. -/
axiom body_ready_ci_function_body_progress_or_diverges_by_cases
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

theorem body_ready_ci_function_body_progress_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyCI Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hready
  exact body_ready_ci_function_body_progress_or_diverges_by_cases hfrag hready

end Cpp
