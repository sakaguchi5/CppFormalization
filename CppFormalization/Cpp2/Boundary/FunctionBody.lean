import CppFormalization.Cpp2.Lemmas.ControlExclusion
import CppFormalization.Cpp2.Static.Inversions

/-!
Return boundary for function bodies.
The raw control semantics remain below; this layer keeps only fallthrough and return.
-/

namespace Cpp

/-- Function-body level exit. This distinguishes plain fallthrough from `return none`. -/
inductive FunctionExit : Type where
  | fellThrough
  | returned (rv : Option Value)

/--
A function-body boundary consumes the raw statement control result.
Only `normal` and `returnResult` survive this boundary.
-/
inductive BigStepFunctionBody : State → CppStmt → FunctionExit → State → Prop where
  | fallthrough {σ σ' : State} {body : CppStmt} :
      BigStepStmt σ body .normal σ' →
      BigStepFunctionBody σ body .fellThrough σ'
  | returning {σ σ' : State} {body : CppStmt} {rv : Option Value} :
      BigStepStmt σ body (.returnResult rv) σ' →
      BigStepFunctionBody σ body (.returned rv) σ'

/--
For a statement that is both break-scoped and continue-scoped, the only
terminating raw control results are `normal` and `returnResult`.
-/
theorem function_body_ctrl_classification
    {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult}
    (hbreak : BreakWellScoped st)
    (hcont : ContinueWellScoped st)
    (h : BigStepStmt σ st ctrl σ') :
    ctrl = .normal ∨ ∃ rv, ctrl = .returnResult rv := by
  cases ctrl with
  | normal =>
      exact Or.inl rfl
  | breakResult =>
      exact False.elim (stmt_break_not_scoped h hbreak)
  | continueResult =>
      exact False.elim (stmt_continue_not_scoped h hcont)
  | returnResult rv =>
      exact Or.inr ⟨rv, rfl⟩

/-- Ideal assumptions already include both scope disciplines, so the same classification follows. -/
theorem function_body_ctrl_classification_of_ideal
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult}
    (hideal : IdealAssumptions Γ σ st)
    (h : BigStepStmt σ st ctrl σ') :
    ctrl = .normal ∨ ∃ rv, ctrl = .returnResult rv := by
  exact function_body_ctrl_classification
    (ideal_assumptions_inv_break_scoped hideal)
    (ideal_assumptions_inv_continue_scoped hideal)
    h

/-- Every well-scoped terminating statement induces a function-body execution. -/
theorem function_body_of_stmt
    {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult}
    (hbreak : BreakWellScoped st)
    (hcont : ContinueWellScoped st)
    (h : BigStepStmt σ st ctrl σ') :
    ∃ ex, BigStepFunctionBody σ st ex σ' := by
  rcases function_body_ctrl_classification hbreak hcont h with hnorm | ⟨rv, hret⟩
  · refine ⟨.fellThrough, ?_⟩
    exact BigStepFunctionBody.fallthrough (by simpa [hnorm] using h)
  · refine ⟨.returned rv, ?_⟩
    exact BigStepFunctionBody.returning (by simpa [hret] using h)

/-- Ideal assumptions version of `function_body_of_stmt`. -/
theorem function_body_of_ideal_assumptions
    {Γ : TypeEnv} {σ σ' : State} {st : CppStmt} {ctrl : CtrlResult}
    (hideal : IdealAssumptions Γ σ st)
    (h : BigStepStmt σ st ctrl σ') :
    ∃ ex, BigStepFunctionBody σ st ex σ' := by
  exact function_body_of_stmt
    (ideal_assumptions_inv_break_scoped hideal)
    (ideal_assumptions_inv_continue_scoped hideal)
    h

/-- Eliminate the function-body wrapper back to raw statement semantics. -/
theorem BigStepFunctionBody.to_stmt
    {σ σ' : State} {st : CppStmt} {ex : FunctionExit}
    (h : BigStepFunctionBody σ st ex σ') :
    match ex with
    | .fellThrough => BigStepStmt σ st .normal σ'
    | .returned rv => BigStepStmt σ st (.returnResult rv) σ' := by
  cases h with
  | fallthrough hstmt =>
      exact hstmt
  | returning hstmt =>
      exact hstmt

@[simp] theorem bigStepFunctionBody_fellThrough_iff
    {σ σ' : State} {st : CppStmt} :
    BigStepFunctionBody σ st .fellThrough σ' ↔ BigStepStmt σ st .normal σ' := by
  constructor
  · intro h
    simpa using BigStepFunctionBody.to_stmt h
  · intro h
    exact .fallthrough h

@[simp] theorem bigStepFunctionBody_returned_iff
    {σ σ' : State} {st : CppStmt} {rv : Option Value} :
    BigStepFunctionBody σ st (.returned rv) σ' ↔ BigStepStmt σ st (.returnResult rv) σ' := by
  constructor
  · intro h
    simpa using BigStepFunctionBody.to_stmt h
  · intro h
    exact .returning h

end Cpp
