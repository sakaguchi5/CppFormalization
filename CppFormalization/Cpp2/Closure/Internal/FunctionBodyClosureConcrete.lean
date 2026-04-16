import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureConcrete

`InternalClosureRoadmapConcrete` までで theorem-backed になった concrete kernel を前提に、
function-body closure の残り open obligations を concrete 側で固定する層。

このファイルの役割は 2 つ:
- 既に theorem-backed な concrete normal-preservation / residual-readiness を closure 主線から読む。
- まだ未証明の function-body case split obligations を、必要最小限の形で切り出す。

ここでは abstract roadmap には戻らない。
-/

/-- Primitive core statements are the statement forms whose closure should reduce to
expr/place progress and primitive preservation alone. -/
def PrimitiveCoreStmtConcrete : CppStmt → Prop
  | .skip => True
  | .exprStmt _ => True
  | .assign _ _ => True
  | .declareObj _ _ _ => True
  | .declareRef _ _ _ => True
  | .breakStmt => True
  | .continueStmt => True
  | .returnStmt _ => True
  | .seq _ _ => False
  | .ite _ _ _ => False
  | .whileStmt _ _ => False
  | .block _ => False

 theorem PrimitiveCoreStmtConcrete.core
    {st : CppStmt} :
    PrimitiveCoreStmtConcrete st → CoreBigStepFragment st := by
  intro h
  cases st <;> simp [PrimitiveCoreStmtConcrete, CoreBigStepFragment, InBigStepFragment] at h ⊢

/-- At function-body top level, `break` and `continue` are excluded by the existing
scope-discipline theorems packaged inside `BodyReady`. -/
theorem top_level_abrupt_excluded_from_bodyReady_concrete
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyReady Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ' := by
  intro hready
  constructor
  · intro hbreak
    exact stmt_break_not_scoped hbreak hready.breakScoped
  · intro hcont
    exact stmt_continue_not_scoped hcont hready.continueScoped

/-
LEGACY SHELL COMMENTED OUT

理由:
- current closure route は CI-centric route へ移っており、
  この concrete shell の高レベル case-driver axiom 群は live 本線では使わない。
- `PrimitiveCoreStmtConcrete` とその basic theorem だけを残し、
  高レベル肩代わりはコメント退避する。

退避対象:
- primitive_stmt_function_body_step_or_diverges_concrete
- seq_function_body_closure_concrete
- ite_function_body_closure_concrete
- block_function_body_closure_concrete
- while_function_body_closure_concrete
- concrete_body_ready_function_body_progress_or_diverges_by_cases_concrete
- concrete_body_ready_function_body_progress_or_diverges_via_cases_concrete

/-- Primitive statements: discharge by expr/place progress and primitive preservation. -/
axiom primitive_stmt_function_body_step_or_diverges_concrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmtConcrete st →
    WellTypedFrom Γ st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/-- Sequence closure: left body classification + theorem-backed normal preservation/readiness
should suffice. This is left as an explicit concrete obligation. -/
axiom seq_function_body_closure_concrete
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    WellTypedFrom Γ (.seq s t) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    (∀ {σ'},
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Γ σ' →
      StmtReadyConcrete Γ σ' t →
      (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨ BigStepStmtDiv σ' t) →
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨ BigStepStmtDiv σ (.seq s t)

/-- Conditional closure still depends on value progress for the condition and closure of the
selected branch. -/
axiom ite_function_body_closure_concrete
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    WellTypedFrom Γ (.ite c s t) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.ite c s t) →
    (StmtReadyConcrete Γ σ s → (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s) →
    (StmtReadyConcrete Γ σ t → (∃ ex σ', BigStepFunctionBody σ t ex σ') ∨ BigStepStmtDiv σ t) →
    (∃ ex σ', BigStepFunctionBody σ (.ite c s t) ex σ') ∨ BigStepStmtDiv σ (.ite c s t)

/-- Block closure: open scope, close scope, and theorem-backed block residual readiness. -/
axiom block_function_body_closure_concrete
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock} :
    WellTypedFrom Γ (.block ss) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.block ss) →
    (∀ {σ'},
      OpenScope σ σ' →
      ScopedTypedStateConcrete (pushTypeScope Γ) σ' →
      BlockReadyConcrete (pushTypeScope Γ) σ' ss →
      (∃ ex σ'', BigStepFunctionBody σ' (.block ss) ex σ'') ∨ BigStepStmtDiv σ' (.block ss)) →
    (∃ ex σ', BigStepFunctionBody σ (.block ss) ex σ') ∨ BigStepStmtDiv σ (.block ss)

/-- While closure: split into false exit, body-normal iteration, body-continue iteration,
and divergence. The residual readiness used here is already theorem-backed concretely,
but the global closure assembly is still isolated as a concrete open obligation. -/
axiom while_function_body_closure_concrete
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    WellTypedFrom Γ (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    (∀ {σ'},
      BigStepStmt σ body .normal σ' →
      ScopedTypedStateConcrete Γ σ' →
      StmtReadyConcrete Γ σ' (.whileStmt c body) →
      (∃ ex σ'', BigStepFunctionBody σ' (.whileStmt c body) ex σ'') ∨ BigStepStmtDiv σ' (.whileStmt c body)) →
    (∀ {σ'},
      BigStepStmt σ body .continueResult σ' →
      ScopedTypedStateConcrete Γ σ' →
      StmtReadyConcrete Γ σ' (.whileStmt c body) →
      (∃ ex σ'', BigStepFunctionBody σ' (.whileStmt c body) ex σ'') ∨ BigStepStmtDiv σ' (.whileStmt c body)) →
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨ BigStepStmtDiv σ (.whileStmt c body)

/-- Concrete case-split master theorem. This is the next genuine theorem target after the
roadmap became concrete and theorem-backed. -/
axiom concrete_body_ready_function_body_progress_or_diverges_by_cases_concrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    WellFormedStmt st →
    WellTypedFrom Γ st →
    BreakWellScoped st →
    ContinueWellScoped st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

theorem concrete_body_ready_function_body_progress_or_diverges_via_cases_concrete
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    WellFormedStmt st →
    WellTypedFrom Γ st →
    BreakWellScoped st →
    ContinueWellScoped st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st := by
  intro hfrag hwf hty hbr hcont hσ hready
  exact
    concrete_body_ready_function_body_progress_or_diverges_by_cases_concrete
      hfrag hwf hty hbr hcont hσ hready
-/

end Cpp
