/-!
# Cpp2.Roadmap.Current

Current roadmap for the semantic-closure refactoring.

This module replaces the old `Closure.Internal.ArchitectureRoadmap` as a modern
roadmap/ledger.  It intentionally contains no broad closure axiom.  Its purpose
is to preserve the design direction while keeping the repository free of the old
Frontier-style assumptions.

Inherited principle from the retired roadmap:
- Do not mix preservation, safety, evaluator adequacy, and bridge contracts in
  one axiom surface.
- Do not use `IdealAssumptions` as the internal closure entry point.
- Normal-path preservation is the meaningful preservation spine; all-control
  preservation is too coarse for the current C++ control semantics.
- Evaluator adequacy, failure semantics, external fragment contracts, and proof
  architecture shells should remain separate.
-/

namespace Cpp
namespace Roadmap
namespace Current

/-- Main layers of the current closure route. -/
inductive MainlineLayer where
  | core
  | static
  | typing
  | semantics
  | lemmas
  | boundary
  | closureFoundation
  | closureInternal
  | closureExternal
  | proof
  deriving DecidableEq, Repr

/-- The four components of the current `BodyClosureBoundaryCI` design. -/
inductive BoundaryLayer where
  /-- Shape and scopedness. -/
  | structural
  /-- Coarse typing, control profile, root witness, and coherence. -/
  | static
  /-- Entry state and concrete readiness. -/
  | dynamic
  /-- Profile soundness against actual executions. -/
  | adequacy
  deriving DecidableEq, Repr

/-- Current high-level refactoring stages. -/
inductive RefactoringStage where
  /-- Keep non-closure, axiom-free foundations outside `Closure` where possible. -/
  | relocateFoundations
  /-- Split global recursion/IH into constructor-specific demand bundles. -/
  | splitCaseDriverDemands
  /-- Make seq tail static/coarse typing theorem-backed. -/
  | theoremizeSeqStaticRoutes
  /-- Separate while tail adequacy from re-entry/dynamic reconstruction. -/
  | splitWhileReentryAndAdequacy
  /-- Isolate true C++ replay/alias contracts from theorem-like transport debt. -/
  | isolateReplayAliasContracts
  /-- Keep public V3 external contracts explicit and canonical. -/
  | stabilizeExternalContracts
  deriving DecidableEq, Repr

/-- Documentation record for planned refactoring work. -/
structure RoadmapEntry where
  stage : RefactoringStage
  title : String
  currentMeaning : String
  doneWhen : String
  deriving Repr

/-!
## Current final target

The active final theorem route is the V3 contract-based reflective/std closure
route.  The internal closure theorem should be assembled from a
`BodyClosureBoundaryCI`-style boundary, not from the retired `IdealAssumptions`
frontier.

## Current boundary discipline

`BodyClosureBoundaryCI` is the canonical internal package:

* `structural` — well-formedness and top-level control scopedness;
* `static` — typing/profile/root/coherence;
* `dynamic` — scoped typed state and concrete readiness;
* `adequacy` — normal/return witness providers for the chosen profile.

## Current frontier discipline

Unresolved obligations should be classified before they are assumed:

* proof architecture shell;
* genuine program contract;
* transport debt;
* replay/alias contract;
* external semantic contract;
* legacy residue.

The current frontier ledger lives in `CppFormalization.Cpp2.Frontier.Current`.
-/

end Current
end Roadmap
end Cpp
