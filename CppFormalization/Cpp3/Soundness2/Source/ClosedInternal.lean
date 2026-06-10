import CppFormalization.Cpp3.Soundness2.Source.Classification

/-!
# CppFormalization.Cpp3.Soundness2.Source.ClosedInternal

Closed-internal source vocabulary for Soundness2.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Closed-internal provider sources.

The provider no longer contains raw `stmtClassify` / `blockClassify` /
`functionBodyClassify` fields.  Those belong to the named classification source
bundle, which itself records the local-control, scope-exit, and loop-behavior
surfaces used by the classifier. -/
structure ClosedInternalProviderSources : Type where
  classification : ClassificationSourceTheorems

namespace ClosedInternalProviderSources

/-- Project local-control sources from the classification bundle. -/
def localControl (P : ClosedInternalProviderSources) : LocalControlSourceTheorems :=
  P.classification.localControl

/-- Project scope-exit sources from the classification bundle. -/
def scopeExit (P : ClosedInternalProviderSources) : ScopeExitSourceTheorems :=
  P.classification.scopeExit

/-- Project loop-behavior sources from the classification bundle. -/
def loopBehavior (P : ClosedInternalProviderSources) : LoopBehaviorCertificateTheorem :=
  P.classification.loopBehavior

end ClosedInternalProviderSources

/-- Closed-internal statement source. -/
structure ClosedInternalStmtSource
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  boundarySource : StmtBoundarySource Γ σ st

namespace ClosedInternalStmtSource

/-- Project the statement boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : ClosedInternalStmtSource Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  h.boundarySource.toBoundary

end ClosedInternalStmtSource

/-- Closed-internal block source. -/
structure ClosedInternalBlockSource
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  boundarySource : BlockBoundarySource Γ σ body

namespace ClosedInternalBlockSource

/-- Project the block boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : ClosedInternalBlockSource Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  h.boundarySource.toBoundary

end ClosedInternalBlockSource

/-- Closed-internal function-body source. -/
structure ClosedInternalFunctionBodySource
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  boundarySource : FunctionBodyBoundarySource Γ σ body

namespace ClosedInternalFunctionBodySource

/-- Project the function-body boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : ClosedInternalFunctionBodySource Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body :=
  h.boundarySource.toBoundary

end ClosedInternalFunctionBodySource

end Source
end Soundness2
end Cpp3
