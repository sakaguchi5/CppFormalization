import CppFormalization.Cpp3.Boundary.Primitive
import CppFormalization.Cpp3.Semantics.Kernel.Stmt

/-!
# CppFormalization.Cpp3.Boundary.Stmt

Runtime entry boundaries for statements, block bodies, and function bodies.

These structures are intentionally entry packages.  They do not say that the
statement terminates, diverges, or preserves later boundaries.
-/

namespace Cpp3
namespace Boundary

/-- Runtime boundary for entering a statement in a concrete state. -/
structure StmtBoundary (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  static : Static.StaticStmtBoundaryInfo Γ st
  effect : Effects.StmtEffect Γ st
  safety : SafetyFragment.StmtSafetyFragment Γ st
  enterable : Prop
  evidence : Contracts.Requires enterable

namespace StmtBoundary

/-- Extract the runtime entry evidence for a statement boundary. -/
def get
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtBoundary Γ σ st) : h.enterable :=
  h.evidence

end StmtBoundary

/-- Runtime boundary for entering a block body in a concrete state. -/
structure BlockBoundary (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  static : Static.StaticBlockBoundaryInfo Γ body
  effect : Effects.BlockEffect Γ body
  safety : SafetyFragment.BlockSafetyFragment Γ body
  enterable : Prop
  evidence : Contracts.Requires enterable

namespace BlockBoundary

/-- Extract the runtime entry evidence for a block boundary. -/
def get
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockBoundary Γ σ body) : h.enterable :=
  h.evidence

end BlockBoundary

/-- Runtime boundary for a function body. -/
structure FunctionBodyBoundary
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  static : Static.StaticFunctionBodyBoundaryInfo Γ body
  effect : Effects.FunctionBodyEffect Γ body
  safety : SafetyFragment.FunctionBodySafetyFragment Γ body
  entry : StmtBoundary Γ σ body

end Boundary
end Cpp3
