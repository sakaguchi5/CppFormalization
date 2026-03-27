import CppFormalization.Cpp2.Closure.Transitions.Minor.StateUpdateRoadmap

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosure

内部主定理
`concrete_body_ready_function_body_progress_or_diverges`
を statement 形ごとの case に分解する青写真。

ポイント:
- closure theorem の主役は raw stmt ではなく function-body 側。
- `break/continue` 漏れは既存 `ControlExclusion` に任せる。
- ここでは各 statement 形ごとに、何を示せば最終定理に到達できるかを固定する。
-/

def PrimitiveCoreStmt : CppStmt → Prop
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

theorem PrimitiveCoreStmt.core
    {st : CppStmt} :
    PrimitiveCoreStmt st → CoreBigStepFragment st := by
  intro h
  cases st <;> simp [PrimitiveCoreStmt, CoreBigStepFragment, InBigStepFragment] at h ⊢

/-- primitive stmt は expr/place progress と primitive preservation で処理する。 -/
axiom primitive_stmt_function_body_step_or_diverges
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    PrimitiveCoreStmt st →
    WellTypedFrom Γ st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/-- sequence は左 stmt の結果で分岐する。 -/
axiom seq_function_body_closure
    {Γ : TypeEnv} {σ : State} {s t : CppStmt} :
    WellTypedFrom Γ (.seq s t) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq s t) →
    (∀ {Δ σ'},
      HasTypeStmt Γ s Δ →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Δ σ' →
      StmtReadyConcrete Δ σ' t →
      (∃ ex σ'', BigStepFunctionBody σ' t ex σ'') ∨ BigStepStmtDiv σ' t) →
    (∃ ex σ', BigStepFunctionBody σ (.seq s t) ex σ') ∨ BigStepStmtDiv σ (.seq s t)

/-- if は条件式進行と分岐先の closure へ還元される。 -/
axiom ite_function_body_closure
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    WellTypedFrom Γ (.ite c s t) →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.ite c s t) →
    (BodyReady Γ σ s → (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s) →
    (BodyReady Γ σ t → (∃ ex σ', BigStepFunctionBody σ t ex σ') ∨ BigStepStmtDiv σ t) →
    (∃ ex σ', BigStepFunctionBody σ (.ite c s t) ex σ') ∨ BigStepStmtDiv σ (.ite c s t)

/-- block は open/close scope と block residual preservation で処理する。 -/
axiom block_function_body_closure
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

/-- while は 0-step exit / body normal loop / body continue loop / divergence に分解される。 -/
axiom while_function_body_closure
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

/-- top-level body では break / continue は既存除外定理で落とす。 -/
axiom top_level_abrupt_excluded_from_bodyReady
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} :
    BodyReady Γ σ st →
    ¬ BigStepStmt σ st .breakResult σ' ∧ ¬ BigStepStmt σ st .continueResult σ'

/-- closure theorem の内部主定理は case split を組み上げたもの。 -/
axiom concrete_body_ready_function_body_progress_or_diverges_by_cases
    {Γ : TypeEnv} {σ : State} {st : CppStmt} :
    CoreBigStepFragment st →
    WellFormedStmt st →
    WellTypedFrom Γ st →
    BreakWellScoped st →
    ContinueWellScoped st →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ st →
    (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/-- 既存 roadmap の内部主定理は case-split 版から得る。 -/
theorem concrete_body_ready_function_body_progress_or_diverges_via_cases
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
  exact concrete_body_ready_function_body_progress_or_diverges_by_cases
    hfrag hwf hty hbr hcont hσ hready

end Cpp
