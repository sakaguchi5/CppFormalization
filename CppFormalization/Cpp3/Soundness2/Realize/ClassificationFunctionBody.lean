import CppFormalization.Cpp3.Soundness2.Realize.ClassificationBoundary
import CppFormalization.Cpp3.Static.ControlAdequacy

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationFunctionBody

Function-body classification from the boundary-level statement classifier.

C++ function bodies do not accept uncaught top-level `break`/`continue`.  That
fact is not proved ad hoc here: it is obtained from the static function-body
control surface plus the lower `Static.ControlAdequacy` theorem saying that any
finite runtime control result of a well-formed statement must be statically
visible.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Boundary-level function-body classifier. -/
structure BoundaryFunctionBodyClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      Boundary.FunctionBodyBoundary Γ σ body →
        Source.ClosedFunctionBodySoundness σ body

namespace BoundaryFunctionBodyClassification

/-- Lift boundary-level statement classification to function-body classification.

The finite `normal` and `return` channels become function-body successes.
Finite top-level `break` and `continue` are impossible by the static function-body
control surface and static/runtime control adequacy.  Divergence is preserved. -/
theorem classify
    (stmt : BoundaryStmtClassifierRealization)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    Source.ClosedFunctionBodySoundness σ body := by
  cases stmt.classify boundary.entry with
  | inl finite =>
      rcases finite with ⟨r, σ₁, step⟩
      cases r with
      | normal =>
          exact Or.inl ⟨.normal, σ₁,
            Semantics.BigStepFunctionBody.normal step⟩
      | breakResult =>
          exact False.elim
            (Static.no_breakResult_of_functionBodyControl
              boundary.static.control
              boundary.static.entry.formed
              step)
      | continueResult =>
          exact False.elim
            (Static.no_continueResult_of_functionBodyControl
              boundary.static.control
              boundary.static.entry.formed
              step)
      | returnResult ov =>
          exact Or.inl ⟨.returned ov, σ₁,
            Semantics.BigStepFunctionBody.returned step⟩
  | inr div =>
      exact Or.inr div

end BoundaryFunctionBodyClassification

namespace BoundaryFunctionBodyClassifierRealization

/-- Build a boundary-level function-body classifier from the boundary-level
statement classifier. -/
def ofStmtClassifier
    (stmt : BoundaryStmtClassifierRealization) :
    BoundaryFunctionBodyClassifierRealization where
  classify := by
    intro Γ σ body boundary
    exact BoundaryFunctionBodyClassification.classify stmt boundary

/-- Recover the existing source-level function-body classifier from the
boundary-level theorem. -/
def toSourceRealization
    (K : BoundaryFunctionBodyClassifierRealization) :
    FunctionBodyClassifierRealization where
  classify := by
    intro Γ σ body source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)

/-- Recover source-level function-body cases from a boundary-level classifier. -/
def toSourceCases
    (K : BoundaryFunctionBodyClassifierRealization) :
    FunctionBodyClassificationCases where
  skip := by
    intro Γ σ source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  exprStmt := by
    intro Γ σ e source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  assign := by
    intro Γ σ a source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  decl := by
    intro Γ σ d source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  seq := by
    intro Γ σ head tail source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  ite := by
    intro Γ σ cond thenBranch elseBranch source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  whileStmt := by
    intro Γ σ cond body source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  block := by
    intro Γ σ body source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)
  jump := by
    intro Γ σ j source
    exact K.classify (Source.FunctionBodyBoundarySource.toBoundary source)

end BoundaryFunctionBodyClassifierRealization

/-- Source-level function-body realization obtained from boundary-level statement
classification and C++ function-body control adequacy. -/
def functionBodyRealization_of_boundaryStmtClassifier
    (stmt : BoundaryStmtClassifierRealization) :
    FunctionBodyClassifierRealization :=
  (BoundaryFunctionBodyClassifierRealization.ofStmtClassifier stmt).toSourceRealization

/-- Source-level function-body case family obtained from boundary-level statement
classification and C++ function-body control adequacy. -/
def functionBodyCases_of_boundaryStmtClassifier
    (stmt : BoundaryStmtClassifierRealization) :
    FunctionBodyClassificationCases :=
  (BoundaryFunctionBodyClassifierRealization.ofStmtClassifier stmt).toSourceCases

end Realize
end Soundness2
end Cpp3
