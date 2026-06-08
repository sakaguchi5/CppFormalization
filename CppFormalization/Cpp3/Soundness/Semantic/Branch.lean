import CppFormalization.Cpp3.Soundness.Semantic.Block

/-!
# CppFormalization.Cpp3.Soundness.Semantic.Branch

Pure semantic propagation lemmas for selected `if` branches.
-/

namespace Cpp3
namespace Soundness
namespace Semantic

/-- Classify an `if` statement from a true condition and a classified then branch. -/
theorem ite_then_of_condition
    {σ σc : State} {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (condStep : Semantics.BigStepCond σ cond true σc)
    (thenSound : ClosedStmtSoundness σc thenBranch) :
    ClosedStmtSoundness σ (.ite cond thenBranch elseBranch) := by
  change Semantics.StmtClassified σ (.ite cond thenBranch elseBranch)
  change Semantics.StmtClassified σc thenBranch at thenSound
  cases thenSound with
  | inr thenDiv =>
      exact Or.inr (Semantics.StmtDiv.iteThen condStep thenDiv)
  | inl thenTerm =>
      rcases thenTerm with ⟨r, σ₁, thenStep⟩
      exact Or.inl ⟨r, σ₁,
        Semantics.BigStepStmt.iteThen condStep thenStep⟩

/-- Classify an `if` statement from a false condition and a classified else branch. -/
theorem ite_else_of_condition
    {σ σc : State} {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (condStep : Semantics.BigStepCond σ cond false σc)
    (elseSound : ClosedStmtSoundness σc elseBranch) :
    ClosedStmtSoundness σ (.ite cond thenBranch elseBranch) := by
  change Semantics.StmtClassified σ (.ite cond thenBranch elseBranch)
  change Semantics.StmtClassified σc elseBranch at elseSound
  cases elseSound with
  | inr elseDiv =>
      exact Or.inr (Semantics.StmtDiv.iteElse condStep elseDiv)
  | inl elseTerm =>
      rcases elseTerm with ⟨r, σ₁, elseStep⟩
      exact Or.inl ⟨r, σ₁,
        Semantics.BigStepStmt.iteElse condStep elseStep⟩

/-- Classify an `if` statement from a then-branch continuation. -/
theorem ite_then_of_continuation
    {Γ Γc : TypeEnv} {σ σc : State}
    {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (cont :
      Continuation.ThenBranchContinuation Γ Γc σ σc cond thenBranch elseBranch)
    (thenSound : ClosedStmtSoundness σc thenBranch) :
    ClosedStmtSoundness σ (.ite cond thenBranch elseBranch) := by
  cases cont with
  | mk stability =>
      cases stability.target with
      | thenBoundary route _condition _preserved _branch =>
          cases route with
          | thenRoute condStep =>
              exact ite_then_of_condition condStep thenSound

/-- Classify an `if` statement from an else-branch continuation. -/
theorem ite_else_of_continuation
    {Γ Γc : TypeEnv} {σ σc : State}
    {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (cont :
      Continuation.ElseBranchContinuation Γ Γc σ σc cond thenBranch elseBranch)
    (elseSound : ClosedStmtSoundness σc elseBranch) :
    ClosedStmtSoundness σ (.ite cond thenBranch elseBranch) := by
  cases cont with
  | mk stability =>
      cases stability.target with
      | elseBoundary route _condition _preserved _branch =>
          cases route with
          | elseRoute condStep =>
              exact ite_else_of_condition condStep elseSound

end Semantic
end Soundness
end Cpp3
