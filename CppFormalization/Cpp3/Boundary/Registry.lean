import CppFormalization.Cpp3.Boundary.Flow

/-!
# CppFormalization.Cpp3.Boundary.Registry

Small registry packages collecting the Boundary surfaces that later Stability,
Continuation, and Soundness layers will consume.
-/

namespace Cpp3
namespace Boundary

/-- Boundary registry for ordinary statement execution. -/
structure StmtBoundaryRegistry (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  entry : StmtBoundary Γ σ st

/-- Boundary registry for block-body execution. -/
structure BlockBoundaryRegistry (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  entry : BlockBoundary Γ σ body

/-- Boundary registry for function-body execution. -/
structure FunctionBodyBoundaryRegistry
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  entry : FunctionBodyBoundary Γ σ body

/-- Boundary registry for sequence continuation. -/
structure SeqContinuationBoundaryRegistry
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  boundary : SeqTailBoundary Γ Θ σ σ₁ head tail

/-- Boundary registry for block-cons continuation. -/
structure BlockContinuationBoundaryRegistry
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  boundary : BlockTailBoundary Γ Θ σ σ₁ head tail

end Boundary
end Cpp3
