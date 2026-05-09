/-!
# Cpp2.Frontier.Current

This module replaces the old `Cpp2.Frontier` files as a *ledger* rather than an
axiom surface.

The old frontier carried broad safety/progress axioms such as "safe statements
terminate or diverge".  That shape is retired.  The current project keeps the
frontier as a classification boundary: it records what kind of unresolved
obligation remains, why it is not yet theorem-backed, and what would remove it.

Policy:
- Do not place coarse semantic safety axioms here.
- Do not reintroduce `IdealAssumptions` as the internal closure entry point.
- Do not use this namespace to bypass the current `BodyClosureBoundaryCI` route.
- Use this namespace only to classify live proof debt and semantic contracts.
-/

namespace Cpp
namespace Frontier
namespace Current

/--
Classification of a current unresolved boundary.

The categories are intentionally semantic rather than file-system oriented:
a proof-architecture shell and a C++ program contract should not look the same.
-/
inductive FrontierKind where
  /-- A shell needed to close the proof architecture, not a C++ program contract. -/
  | proofArchitectureShell
  /-- A genuine condition the program or fragment must maintain. -/
  | programContract
  /-- A theorem-like transport obligation that should not be assumed as a contract too early. -/
  | transportDebt
  /-- Replay/aliasing/separation obligation, usually expressing a real C++ safety condition. -/
  | replayAliasContract
  /-- Public-facing contract imposed on std/reflection/external fragments. -/
  | externalContract
  /-- Old compatibility surface retained only while callers are migrated. -/
  | legacyResidue
  deriving DecidableEq, Repr

/--
A lightweight documentation record for frontier entries.

This is deliberately data-only.  It does not assert the unresolved obligation;
it records how the obligation should be understood during refactoring.
-/
structure FrontierEntry where
  name : String
  kind : FrontierKind
  currentLocation : String
  meaning : String
  removalCriterion : String
  deriving Repr

/--
Canonical labels used when documenting the current frontier.
-/
def proofArchitectureShell : FrontierKind := .proofArchitectureShell
def programContract : FrontierKind := .programContract
def transportDebt : FrontierKind := .transportDebt
def replayAliasContract : FrontierKind := .replayAliasContract
def externalContract : FrontierKind := .externalContract
def legacyResidue : FrontierKind := .legacyResidue

/-!
## Current reading guide

The old frontier files are retired because their axioms were too coarse:
primitive preservation, expression progress, statement closure, and external
fragment soundness were all mixed together.

The current frontier should instead be read as follows:

* `proofArchitectureShell` — examples include global recursion principles such
  as the case-driver IH.  These are proof-structure issues, not C++ contracts.
* `programContract` — examples include loop re-entry invariants that really say
  the next iteration is safe.
* `transportDebt` — examples include post-state adequacy transport that may be
  theorem-backed once the profile/static route is precise enough.
* `replayAliasContract` — examples include dereference/assignment replay and
  separation witnesses.
* `externalContract` — examples include canonical normal/return adequacy
  required from public V3 fragment routes.
* `legacyResidue` — examples include unconditional compatibility wrappers that
  have already been superseded by condition-first or route-aware theorems.
-/

end Current
end Frontier
end Cpp
