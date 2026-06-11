import CppFormalization.Cpp3.Soundness2.Realize.ClassificationBoundary
import CppFormalization.Cpp3.Static.ControlAdequacy

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationFunctionBody

Function-body classifier layer.

After the boundary-level statement classifier is available, function-body
classification is a C++-specific lift: top-level `break` and `continue` are ruled
out by function-body static control adequacy.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Source-level realized classifier for closed-internal function bodies. -/
structure FunctionBodyClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      Source.FunctionBodyBoundarySource Γ σ body →
        Source.ClosedFunctionBodySoundness σ body

/-- Boundary-level function-body classifier. -/
structure BoundaryFunctionBodyClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      Boundary.FunctionBodyBoundary Γ σ body →
        Source.ClosedFunctionBodySoundness σ body

namespace BoundaryFunctionBodyClassification

/-- Lift boundary-level statement classification to function-body classification. -/
theorem classify
    (stmt : BoundaryStmtClassifierRealization)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    Source.ClosedFunctionBodySoundness σ body := by
  exact
    Semantics.functionBodyClassified_of_stmtClassified
      (stmt.classify boundary.entry)
      (by
        intro σ₁ step
        exact
          Static.no_breakResult_of_functionBodyControl
            boundary.static.control
            boundary.static.entry.formed
            step)
      (by
        intro σ₁ step
        exact
          Static.no_continueResult_of_functionBodyControl
            boundary.static.control
            boundary.static.entry.formed
            step)

end BoundaryFunctionBodyClassification

namespace BoundaryFunctionBodyClassifierRealization

/-- Build a boundary-level function-body classifier from the boundary statement core. -/
def ofStmtClassifier
    (stmt : BoundaryStmtClassifierRealization) :
    BoundaryFunctionBodyClassifierRealization where
  classify := by
    intro Γ σ body boundary
    exact BoundaryFunctionBodyClassification.classify stmt boundary

/-- Recover the source-level function-body classifier from the boundary-level core. -/
def toSourceRealization
    (K : BoundaryFunctionBodyClassifierRealization) :
    FunctionBodyClassifierRealization where
  classify := by
    intro Γ σ body source
    exact K.classify source.toBoundary

end BoundaryFunctionBodyClassifierRealization

/-- Source-level function-body realization obtained from boundary-level statement
classification and C++ function-body control adequacy. -/
def functionBodyRealization_of_boundaryStmtClassifier
    (stmt : BoundaryStmtClassifierRealization) :
    FunctionBodyClassifierRealization :=
  (BoundaryFunctionBodyClassifierRealization.ofStmtClassifier stmt).toSourceRealization

end Realize
end Soundness2
end Cpp3
