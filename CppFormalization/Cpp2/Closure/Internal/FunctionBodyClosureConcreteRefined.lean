import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureConcreteRefined

`FunctionBodyClosureConcrete` の case-split 設計を保ちつつ、
function-body top level に本当に必要な境界前提を明示した refined 版。

重要:
- `seq / ite / block / while` の closure は、単なる
  `WellTypedFrom + ScopedTypedStateConcrete + StmtReadyConcrete`
  だけでは一般に成り立たない。
- function-body top level では `break / continue` 漏れを禁止する
  scope discipline が本質なので、それを `BodyReadyConcrete` にまとめる。
- これは abstract `BodyReady` の concrete sibling であり、
  後で abstract 層へ上げる橋にもなる。
-/

/-- Concrete-side body boundary contract. -/
structure BodyReadyConcrete (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop where
  wf : WellFormedStmt st
  typed : WellTypedFrom Γ st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ st

/-- Concrete body readiness drops to the abstract body boundary. -/
theorem bodyReady_of_bodyReadyConcrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    BodyReadyConcrete Γ σ st → BodyReady Γ σ st := by
  intro h
  refine {
    wf := h.wf
    typed := h.typed
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped
    state := scopedTypedState_of_concrete h.state
    safe := stmtReady_of_concrete h.safe
  }

/-- Concrete top-level abrupt exclusion is just the abstract one, via the bridge. -/
theorem top_level_abrupt_excluded_from_bodyReadyConcrete
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyReadyConcrete Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro hready
  exact top_level_abrupt_excluded_from_bodyReady_concrete (bodyReady_of_bodyReadyConcrete hready)

/-- Primitive case, now phrased with the honest function-body boundary premise. -/
axiom primitive_stmt_function_body_step_or_diverges_concrete_refined
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmtConcrete st →
    BodyReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/-- Sequence closure with the honest top-level boundary contract. -/
axiom seq_function_body_closure_concrete_refined
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    BodyReadyConcrete Γ σ (.seq s t) →
    (∀ {σ'},
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Γ σ' →
      StmtReadyConcrete Γ σ' t →
      BodyReadyConcrete Γ σ' t →
      (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨ BigStepStmtDiv σ' t) →
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨ BigStepStmtDiv σ (.seq s t)

/-- Conditional closure with the honest top-level boundary contract. -/
axiom ite_function_body_closure_concrete_refined
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    BodyReadyConcrete Γ σ (.ite c s t) →
    (BodyReadyConcrete Γ σ s → (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s) →
    (BodyReadyConcrete Γ σ t → (∃ ex σ', BigStepFunctionBody σ t ex σ') ∨ BigStepStmtDiv σ t) →
    (∃ ex σ', BigStepFunctionBody σ (.ite c s t) ex σ') ∨ BigStepStmtDiv σ (.ite c s t)

/-- Block closure with the honest top-level boundary contract. -/
axiom block_function_body_closure_concrete_refined
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    BodyReadyConcrete Γ σ (.block ss) →
    (∀ {σ'},
      OpenScope σ σ' →
      ScopedTypedStateConcrete (pushTypeScope Γ) σ' →
      BlockReadyConcrete (pushTypeScope Γ) σ' ss →
      (∃ ex σ'', BigStepFunctionBody σ' (.block ss) ex σ'') ∨ BigStepStmtDiv σ' (.block ss)) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨ BigStepStmtDiv σ (.block ss)

/-- While closure with the honest top-level boundary contract. -/
axiom while_function_body_closure_concrete_refined
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyReadyConcrete Γ σ (.whileStmt c body) →
    (∀ {σ'},
      BigStepStmt σ body .normal σ' →
      ScopedTypedStateConcrete Γ σ' →
      StmtReadyConcrete Γ σ' (.whileStmt c body) →
      BodyReadyConcrete Γ σ' (.whileStmt c body) →
      (∃ ex σ'', BigStepFunctionBody σ' (.whileStmt c body) ex σ'') ∨ BigStepStmtDiv σ' (.whileStmt c body)) →
    (∀ {σ'},
      BigStepStmt σ body .continueResult σ' →
      ScopedTypedStateConcrete Γ σ' →
      StmtReadyConcrete Γ σ' (.whileStmt c body) →
      BodyReadyConcrete Γ σ' (.whileStmt c body) →
      (∃ ex σ'', BigStepFunctionBody σ' (.whileStmt c body) ex σ'') ∨ BigStepStmtDiv σ' (.whileStmt c body)) →
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨ BigStepStmtDiv σ (.whileStmt c body)

/-- Refined concrete master theorem target. -/
axiom concrete_body_ready_function_body_progress_or_diverges_by_cases_concrete_refined
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    BodyReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

end Cpp
