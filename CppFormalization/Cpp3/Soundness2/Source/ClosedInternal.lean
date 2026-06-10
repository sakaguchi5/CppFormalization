import CppFormalization.Cpp3.Soundness2.Source.LoopBehavior

/-!
# CppFormalization.Cpp3.Soundness2.Source.ClosedInternal

Closed-internal source vocabulary and final target names for Soundness2.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Soundness target for a closed internal statement. -/
abbrev ClosedStmtSoundness (σ : State) (st : CppStmt) : Prop :=
  Semantics.StmtClassified σ st

/-- Soundness target for a closed internal block body. -/
abbrev ClosedBlockSoundness (σ : State) (body : StmtBlock) : Prop :=
  Semantics.BlockClassified σ body

/-- Soundness target for a closed internal function body. -/
abbrev ClosedFunctionBodySoundness (σ : State) (body : CppStmt) : Prop :=
  Semantics.FunctionBodyClassified σ body

/-- Closed-internal provider sources.

The local-control, scope-exit, and loop-behavior sources remain visible.  The
three classification fields are the final lower theorems consumed by Soundness2;
this avoids importing the old Soundness proof while keeping the final theorem
honest and conditional on explicit source theorems. -/
structure ClosedInternalProviderSources : Type where
  localControl : LocalControlSourceTheorems
  scopeExit : ScopeExitSourceTheorems
  loopBehavior : LoopBehaviorCertificateTheorem
  stmtClassify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      StmtBoundarySource Γ σ st →
        ClosedStmtSoundness σ st
  blockClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      BlockBoundarySource Γ σ body →
        ClosedBlockSoundness σ body
  functionBodyClassify :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      FunctionBodyBoundarySource Γ σ body →
        ClosedFunctionBodySoundness σ body

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
