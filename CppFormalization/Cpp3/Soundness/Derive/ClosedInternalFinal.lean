import CppFormalization.Cpp3.Soundness.DerivedLoopFinal
import CppFormalization.Cpp3.Soundness.Derive.BoundaryConstruction.Core
import CppFormalization.Cpp3.Soundness.Derive.BoundaryConstruction.Flow
import CppFormalization.Cpp3.Soundness.Derive.LocalCorridors.Constructors
import CppFormalization.Cpp3.Soundness.Derive.ScopeExit.Constructors
import CppFormalization.Cpp3.Soundness.Derive.LoopEngine.BehaviorSource

/-!
# CppFormalization.Cpp3.Soundness.Derive.ClosedInternalFinal

Phase 5: closed-internal final assembly.

The previous phases fixed the bottom-up construction direction:

* Phase 1: operational loop traces build progress certificates and loop-engine cases;
* Phase 2: C++ loop behavior sources explain finite/body-divergent/forever loops;
* Phase 3: local-control and scope-exit facts are built from concrete sources;
* Phase 4: runtime boundaries are built from typing/static/effect/safety/runtime
  entry evidence, and selected post-state boundaries are packaged as stability.

This file does not introduce a new semantic rule and it does not talk about the
external world.  It merely assembles the closed-internal construction sources into
`DerivedLoopFinal`'s final soundness surface.

C++ reading: for the internal fragment, once a program point has a constructed
runtime boundary and the local-control, scope-exit, and loop-behavior construction
sources are available, the program is classified as finite success or legitimate
divergence, and therefore is not unclassified stuck.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace ClosedInternal

/-- Bottom-up provider sources for the closed internal fragment.

These are the construction sources produced by Phases 1--4, kept in their C++
meaningful form rather than collapsed into opaque final providers. -/
structure ClosedInternalProviderSources : Type where
  localControl : LocalCorridors.LocalControlSourceTheorems
  scopeExit : ScopeExit.ScopeExitSourceTheorems
  loopBehavior : LoopEngine.LoopBehaviorCertificateTheorem

namespace ClosedInternalProviderSources

/-- Assemble the source-level provider bundle into the final provider bundle
consumed by `DerivedLoopFinal`. -/
def toDerivedLoopProviders
    (P : ClosedInternalProviderSources) :
    Cpp3.Soundness.Final.DerivedLoopClosedSoundnessProviders where
  localControl :=
    LocalCorridors.localControlConstructionTheorems_of_sources P.localControl
  scopeExit :=
    ScopeExit.scopeExitConstructionTheorems_of_sources P.scopeExit
  loopProgress :=
    LoopEngine.loopProgressCertificateTheorem_of_behaviorCertificate P.loopBehavior

end ClosedInternalProviderSources

/-- Closed-internal statement source.

The boundary is not assumed as a monolith: it is the Phase-4 source containing
static/typing, effects, safety-fragment obligations, and concrete runtime entry
evidence. -/
structure ClosedInternalStmtSource
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  boundarySource : BoundaryConstruction.StmtBoundarySource Γ σ st

namespace ClosedInternalStmtSource

/-- Build the concrete statement boundary from the closed-internal source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : ClosedInternalStmtSource Γ σ st) :
    Boundary.StmtBoundary Γ σ st :=
  BoundaryConstruction.StmtBoundarySource.toBoundary h.boundarySource

end ClosedInternalStmtSource

/-- Closed-internal block-body source. -/
structure ClosedInternalBlockSource
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Type where
  boundarySource : BoundaryConstruction.BlockBoundarySource Γ σ body

namespace ClosedInternalBlockSource

/-- Build the concrete block boundary from the closed-internal source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : ClosedInternalBlockSource Γ σ body) :
    Boundary.BlockBoundary Γ σ body :=
  BoundaryConstruction.BlockBoundarySource.toBoundary h.boundarySource

end ClosedInternalBlockSource

/-- Closed-internal function-body source.

This is the final C++-facing input for the internal fragment: statement typing is
kept visible inside the Phase-4 function-body boundary source, but runtime entry
is still supplied by an actual constructed statement boundary. -/
structure ClosedInternalFunctionBodySource
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Type where
  boundarySource : BoundaryConstruction.FunctionBodyBoundarySource Γ σ body

namespace ClosedInternalFunctionBodySource

/-- Build the concrete function-body boundary from the closed-internal source. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : ClosedInternalFunctionBodySource Γ σ body) :
    Boundary.FunctionBodyBoundary Γ σ body :=
  BoundaryConstruction.FunctionBodyBoundarySource.toBoundary h.boundarySource

end ClosedInternalFunctionBodySource

/-- Closed-internal statement soundness from bottom-up construction sources. -/
theorem closedStmtSoundness
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : ClosedInternalStmtSource Γ σ st) :
    ClosedStmtSoundness σ st :=
  Cpp3.Soundness.Final.closedStmtSoundness_derivedLoop
    (P.toDerivedLoopProviders)
    source.toBoundary

/-- Closed-internal block-body soundness from bottom-up construction sources. -/
theorem closedBlockSoundness
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : ClosedInternalBlockSource Γ σ body) :
    ClosedBlockSoundness σ body :=
  Cpp3.Soundness.Final.closedBlockSoundness_derivedLoop
    (P.toDerivedLoopProviders)
    source.toBoundary

/-- Closed-internal function-body soundness from bottom-up construction sources. -/
theorem closedFunctionBodySoundness
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : ClosedInternalFunctionBodySource Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  Cpp3.Soundness.Final.closedFunctionBodySoundness_derivedLoop
    (P.toDerivedLoopProviders)
    source.toBoundary

/-- Closed-internal statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : ClosedInternalStmtSource Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  Cpp3.Soundness.Final.noStmtUnclassifiedStuck_derivedLoop
    (P.toDerivedLoopProviders)
    source.toBoundary

/-- Closed-internal block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : ClosedInternalBlockSource Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  Cpp3.Soundness.Final.noBlockUnclassifiedStuck_derivedLoop
    (P.toDerivedLoopProviders)
    source.toBoundary

/-- Closed-internal function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : ClosedInternalFunctionBodySource Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  Cpp3.Soundness.Final.noFunctionBodyUnclassifiedStuck_derivedLoop
    (P.toDerivedLoopProviders)
    source.toBoundary

/-- Combined closed-internal statement result. -/
structure ClosedInternalStmtResult
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : ClosedInternalStmtSource Γ σ st) : Type where
  soundness : ClosedStmtSoundness σ st := closedStmtSoundness P source
  noUnclassifiedStuck : ¬ Semantics.StmtUnclassifiedStuck σ st :=
    noStmtUnclassifiedStuck P source

/-- Combined closed-internal block-body result. -/
structure ClosedInternalBlockResult
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : ClosedInternalBlockSource Γ σ body) : Type where
  soundness : ClosedBlockSoundness σ body := closedBlockSoundness P source
  noUnclassifiedStuck : ¬ Semantics.BlockUnclassifiedStuck σ body :=
    noBlockUnclassifiedStuck P source

/-- Combined closed-internal function-body result. -/
structure ClosedInternalFunctionBodyResult
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : ClosedInternalFunctionBodySource Γ σ body) : Type where
  soundness : ClosedFunctionBodySoundness σ body :=
    closedFunctionBodySoundness P source
  noUnclassifiedStuck : ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
    noFunctionBodyUnclassifiedStuck P source

/-- Package the statement result as a single object. -/
def closedStmtResult
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (source : ClosedInternalStmtSource Γ σ st) :
    ClosedInternalStmtResult P source where

/-- Package the block-body result as a single object. -/
def closedBlockResult
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (source : ClosedInternalBlockSource Γ σ body) :
    ClosedInternalBlockResult P source where

/-- Package the function-body result as a single object. -/
def closedFunctionBodyResult
    (P : ClosedInternalProviderSources)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (source : ClosedInternalFunctionBodySource Γ σ body) :
    ClosedInternalFunctionBodyResult P source where

end ClosedInternal
end Derive
end Soundness
end Cpp3
