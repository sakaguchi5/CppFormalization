import CppFormalization.Cpp3.Stability.Primitive
import CppFormalization.Cpp3.Semantics.Kernel.Classification

/-!
# CppFormalization.Cpp3.Stability.Stmt

Statement and block result stability packages.

These are result-level stability surfaces: they say that a statement/block
execution result is compatible with the runtime boundary evidence carried into
it.  They are not the final progress/soundness theorem.
-/

namespace Cpp3
namespace Stability

/-- Stability package for a finite statement result. -/
structure StmtResultStability
    (Γ : TypeEnv) (σ σ₁ : State) (st : CppStmt) (r : CtrlResult) : Type where
  entry : Boundary.StmtBoundary Γ σ st
  step : Semantics.BigStepStmt σ st r σ₁
  certificate : StabilityCertificate .stabilityDerived

/-- Stability package for a finite block-body result. -/
structure BlockResultStability
    (Γ : TypeEnv) (σ σ₁ : State) (body : StmtBlock) (r : CtrlResult) : Type where
  entry : Boundary.BlockBoundary Γ σ body
  step : Semantics.BigStepBlock σ body r σ₁
  certificate : StabilityCertificate .stabilityDerived

/-- Stability package for a function-body finite success result. -/
structure FunctionBodyResultStability
    (Γ : TypeEnv) (σ σ₁ : State) (body : CppStmt) (ok : ProgSuccess) : Type where
  entry : Boundary.FunctionBodyBoundary Γ σ body
  step : Semantics.BigStepFunctionBody σ body ok σ₁
  certificate : StabilityCertificate .stabilityDerived

/-- Stability package for statement divergence.

A diverging statement has no final post-state, but the stability layer may still
carry the boundary facts needed to justify every selected finite prefix. -/
structure StmtDivergenceStability
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  entry : Boundary.StmtBoundary Γ σ st
  div : Semantics.StmtDiv σ st
  certificate : StabilityCertificate .stabilityDerived

/-- Stability package for block-body divergence. -/
structure BlockDivergenceStability
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  entry : Boundary.BlockBoundary Γ σ body
  div : Semantics.BlockDiv σ body
  certificate : StabilityCertificate .stabilityDerived

end Stability
end Cpp3
