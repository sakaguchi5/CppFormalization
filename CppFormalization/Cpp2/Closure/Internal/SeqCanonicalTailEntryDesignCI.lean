import CppFormalization.Cpp2.Closure.Internal.SeqResidualAdequacyRouteRefinementCI

namespace Cpp

/-!
# Closure.Internal.SeqCanonicalTailEntryDesignCI

A natural design for the two remaining `seq` questions:

1. Where does selected-route tail static typing come from?
2. Why does the recursive tail boundary use the same static profile as the
   selected route?

The design answer is:

* tail static typing is a **static-route certificate** attached to the sequence
  static construction;
* recursive tail entry should not be allowed to choose an arbitrary static
  boundary.  It should be entered through a boundary indexed by the already
  selected static boundary.

C++ reading: in `s; t`, after `s` falls through normally, the program continues
with `t` in the post type-environment selected by the typing rule for that
particular normal exit.  The recursive/case-driver tail call must use that same
static analysis of `t`; otherwise the semantic adequacy being reused would be
about the wrong profile.
-/

/-!
## 1. Static route certificate for the selected tail

This is the precise home for “where tail static typing comes from”.

It is not a runtime invariant and not a semantic adequacy axiom.  It is a static
certificate for a sequence entry: every selected left-normal payload has a
selected-tail static source.
-/

/--
Per-entry static-route certificate for the tail of a sequence.

The canonical decomposition and normal-slot selection are fixed by the existing
static route machinery.  The certificate only supplies the selected tail source
for each selected left-normal payload.
-/
structure SeqTailStaticRouteCertificateAtEntryCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) : Type where
  source :
    ∀ (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile),
      let D := seq_static_decomposition_ci_of_entry hentry
      let N := seq_left_normal_slot_selection_ci_of_decomposition hentry D
      SeqSelectedTailStaticSourceAtSelectionCI hentry D N hp

namespace SeqTailStaticRouteCertificateAtEntryCI

/-- Extract canonical source coverage for a fixed entry. -/
def sourceAt
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    (C : SeqTailStaticRouteCertificateAtEntryCI hentry)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) :
    let D := seq_static_decomposition_ci_of_entry hentry
    let N := seq_left_normal_slot_selection_ci_of_decomposition hentry D
    SeqSelectedTailStaticSourceAtSelectionCI hentry D N hp :=
  C.source hp

end SeqTailStaticRouteCertificateAtEntryCI

/--
Global provider form of the per-entry certificate.

Long-term, this should be constructed together with sequence static
decomposition/slot selection.  It is a static-analysis provider, not a C++
runtime contract.
-/
structure SeqTailStaticRouteCertificateProviderCI : Type where
  certificate :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)),
      SeqTailStaticRouteCertificateAtEntryCI hentry

namespace SeqTailStaticRouteCertificateProviderCI

/--
Forget the explicit certificate-provider presentation to the existing canonical
source coverage interface.
-/
noncomputable def toCanonicalSourceCoverage
    (C : SeqTailStaticRouteCertificateProviderCI) :
    SeqCanonicalSelectedTailStaticSourceCoverageCI :=
  { source := by
      intro Γ σ s t hentry hp
      exact (C.certificate hentry).source hp }

/--
The selected-route tail static typing object produced by the static certificate.
-/
noncomputable def toRouteTyping
    (C : SeqTailStaticRouteCertificateProviderCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  seqSelectedTailStaticRouteTypingCI_of_staticSources
    C.toCanonicalSourceCoverage

/--
The coarse selected-tail typing support is a projection of the same static
certificate.
-/
noncomputable def toCoarseTyping
    (C : SeqTailStaticRouteCertificateProviderCI) :
    SeqTailCoarseTypingAtSelectedNormalCI :=
  seqTailCoarseTypingAtSelectedNormalCI_of_canonicalStaticSources
    C.toCanonicalSourceCoverage

/--
The old tail-return `typed0` support is also just a projection of the static
certificate.
-/
noncomputable def toTailReturnTyped0Support
    (C : SeqTailStaticRouteCertificateProviderCI) :
    SeqTailReturnTyped0SupportCI :=
  seqTailReturnTyped0SupportCI_of_canonicalStaticSources
    C.toCanonicalSourceCoverage

end SeqTailStaticRouteCertificateProviderCI

/-!
## 2. Boundaries indexed by a fixed static boundary

This is the precise home for “why does the recursive tail boundary have the same
static profile as the selected route?”.

Do not ask a recursive call to produce an arbitrary `BodyClosureBoundaryCI`.
Ask it to produce a boundary **at the selected static boundary**.  Then the
static equality is definitional.
-/

/--
A closure boundary whose static component is fixed by the caller.

This is only a view of `BodyClosureBoundaryCI`; it prevents the recursive side
from silently choosing a different static profile.
-/
structure BodyClosureBoundaryAtStaticCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (static : BodyStaticBoundaryCI Γ st) : Type where
  structural : BodyStructuralBoundary Γ st
  dynamic : BodyDynamicBoundary Γ σ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

namespace BodyClosureBoundaryAtStaticCI

/-- Forget the fixed-static view to the ordinary boundary. -/
def toBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {static : BodyStaticBoundaryCI Γ st}
    (B : BodyClosureBoundaryAtStaticCI Γ σ st static) :
    BodyClosureBoundaryCI Γ σ st :=
  { structural := B.structural
    static := static
    dynamic := B.dynamic
    adequacy := B.adequacy }

@[simp] theorem toBoundary_static
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {static : BodyStaticBoundaryCI Γ st}
    (B : BodyClosureBoundaryAtStaticCI Γ σ st static) :
    B.toBoundary.static = static := rfl

/-- Repackage an ordinary boundary at its own static component. -/
def ofBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (B : BodyClosureBoundaryCI Γ σ st) :
    BodyClosureBoundaryAtStaticCI Γ σ st B.static :=
  { structural := B.structural
    dynamic := B.dynamic
    adequacy := B.adequacy }

end BodyClosureBoundaryAtStaticCI

/--
Selected-payload tail entry through a fixed selected static route.

This is the natural recursive surface for the lower static-route payload design:
given the selected normal payload `hp`, produce the tail boundary at exactly
`T.static hentry hp`.
-/
structure SeqSelectedTailFixedStaticBoundaryCI
    (T : SeqSelectedTailStaticRouteTypingCI)
    (_P : StmtNormalPreservationCoreCI) : Type where
  boundaryAt :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyClosureBoundaryAtStaticCI hp.Θ σ1 t (T.static hentry hp)

namespace SeqSelectedTailFixedStaticBoundaryCI

/--
Forget fixed-static selected-payload boundary support to the previous alignment
surface.  The static equality is now `rfl`.
-/
noncomputable def toBoundaryForStaticRouteTyping
    {T : SeqSelectedTailStaticRouteTypingCI}
    {P : StmtNormalPreservationCoreCI}
    (B : SeqSelectedTailFixedStaticBoundaryCI T P) :
    SeqSelectedTailBoundaryForStaticRouteTypingCI T P :=
  { boundary := by
      intro Γ σ σ1 s t hentry hstepHead hp
      exact (B.boundaryAt hentry hstepHead hp).toBoundary
    static_eq := by
      intro Γ σ σ1 s t hentry hstepHead hp
      rfl }

/--
Project selected-tail adequacy from fixed-static recursive boundary support.
-/
noncomputable def toTailAdequacy
    {T : SeqSelectedTailStaticRouteTypingCI}
    {P : StmtNormalPreservationCoreCI}
    (B : SeqSelectedTailFixedStaticBoundaryCI T P) :
    SeqSelectedTailAdequacyForStaticRouteTypingCI T P :=
  B.toBoundaryForStaticRouteTyping.toTailAdequacy

/--
Assemble the current static-route payload from direct left adequacy and a
fixed-static recursive tail boundary.
-/
noncomputable def toStaticRoutePayload
    {T : SeqSelectedTailStaticRouteTypingCI}
    {P : StmtNormalPreservationCoreCI}
    (B : SeqSelectedTailFixedStaticBoundaryCI T P) :
    SeqSelectedHeadNormalRoutePayloadStaticRouteCI P :=
  seqSelectedHeadNormalRoutePayloadStaticRouteCI_of_directLeftAdequacy
    T B.toTailAdequacy

end SeqSelectedTailFixedStaticBoundaryCI

/--
Route-level tail entry through the route-projected static boundary.

This is the natural case-driver surface: after route selection, the recursive
tail boundary is required at exactly the static boundary projected from that
route.
-/
structure SeqTailFixedStaticBoundaryAtSelectedRouteCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  boundaryAtRoute :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (route : SeqHeadNormalRouteCI Γ σ s t σ1
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyClosureBoundaryAtStaticCI route.Θ σ1 t
        (seq_tail_static_boundary_ci_of_head_normal_route_projected
          hentry hstepHead route)

namespace SeqTailFixedStaticBoundaryAtSelectedRouteCI

/--
Forget fixed-static route-boundary support to the previous selected-route
alignment surface.  Again, the static equality is definitional.
-/
noncomputable def toBoundaryForSelectedRoute
    {P : StmtNormalPreservationCoreCI}
    (B : SeqTailFixedStaticBoundaryAtSelectedRouteCI P) :
    SeqTailBoundaryForSelectedRouteCoreSupportCI P :=
  { boundary := by
      intro Γ σ σ1 s t hentry hstepHead route
      exact (B.boundaryAtRoute hentry hstepHead route).toBoundary
    static_eq := by
      intro Γ σ σ1 s t hentry hstepHead route
      rfl }

/--
Boundary-level sequence support from direct left adequacy plus fixed-static tail
entry at the selected route.
-/
noncomputable def toBoundaryCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (B : SeqTailFixedStaticBoundaryAtSelectedRouteCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_directLeftAndRouteTailBoundary
    B.toBoundaryForSelectedRoute

end SeqTailFixedStaticBoundaryAtSelectedRouteCI

/-!
## Final design package

This package is the “axiom-shaped” design, but with the two responsibilities in
their natural places:

* `staticProvider` is produced by sequence static typing/slot decomposition;
* `tailBoundary` is produced by recursive closure/case-driver at the fixed
  selected static boundary.
-/

/--
Natural seq design package at the selected-payload/static-route level.
-/
structure SeqCanonicalTailEntryDesignCI
    (P : StmtNormalPreservationCoreCI) : Type where
  staticProvider : SeqTailStaticRouteCertificateProviderCI
  tailBoundary :
    SeqSelectedTailFixedStaticBoundaryCI staticProvider.toRouteTyping P

namespace SeqCanonicalTailEntryDesignCI

/-- The selected-route payload induced by the natural design package. -/
noncomputable def toStaticRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (D : SeqCanonicalTailEntryDesignCI P) :
    SeqSelectedHeadNormalRoutePayloadStaticRouteCI P :=
  D.tailBoundary.toStaticRoutePayload

/-- The boundary-level sequence support induced by the natural design package. -/
noncomputable def toBoundaryCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (D : SeqCanonicalTailEntryDesignCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_staticRoutePayload
    D.toStaticRoutePayload

end SeqCanonicalTailEntryDesignCI

end Cpp
