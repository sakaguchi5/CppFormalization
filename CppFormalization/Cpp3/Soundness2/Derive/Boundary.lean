import CppFormalization.Cpp3.Soundness2.Source.Boundary

/-!
# CppFormalization.Cpp3.Soundness2.Derive.Boundary

Boundary derivations from Soundness2 source objects.
-/

namespace Cpp3
namespace Soundness2
namespace Derive

/-- Derive a concrete statement boundary from a statement boundary source. -/
def stmtBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : Source.StmtBoundarySource Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  source.toBoundary

/-- Derive a concrete block boundary from a block boundary source. -/
def blockBoundary
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : Source.BlockBoundarySource Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  source.toBoundary

/-- Derive a concrete function-body boundary from a function-body source. -/
def functionBodyBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : Source.FunctionBodyBoundarySource Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body :=
  source.toBoundary

end Derive
end Soundness2
end Cpp3
