import CppFormalization.Cpp2.Closure.Internal.SeqCanonicalTailEntryCompatibilityCI

namespace Cpp

/-!
# Closure.Internal.SeqCanonicalTailEntryMainlineSupportCI

Mainline-facing support package for the fixed-static `seq` design.

The previous file connected each component separately:

* static-route certificates can be obtained from existing selected-tail static
  source coverage;
* fixed-static route tail boundaries can be obtained from the current
  route-theorem-backed support.

This file packages those two facts into the shape that the function-body
case-driver wants to consume.

C++ reading: for `s; t`, the `seq` case-driver needs two independent services.

1. Static service:
   determine the static boundary for `t` from the selected normal exit of `s`.

2. Recursive tail-entry service:
   enter `t` through exactly that selected static boundary, not through an
   arbitrary freshly chosen profile.

The actual `Seq.close` boundary support uses the second service directly.  The
first service remains visible in the package so the static route is still a
first-class theorem-backed component, not hidden inside route payloads.
-/

/--
Mainline-facing package for the canonical tail-entry design.

`staticProvider` answers the static question:
where does the selected tail static boundary come from?

`routeTailBoundary` answers the recursive/case-driver question:
how do we enter the tail through the selected route static boundary?
-/
structure SeqCanonicalTailEntryMainlineSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  staticProvider : SeqTailStaticRouteCertificateProviderCI
  routeTailBoundary : SeqTailFixedStaticBoundaryAtSelectedRouteCI P

namespace SeqCanonicalTailEntryMainlineSupportCI

/-- Extract the selected-tail static route typing induced by the static provider. -/
noncomputable def tailStaticRouteTyping
    {P : StmtNormalPreservationCoreCI}
    (S : SeqCanonicalTailEntryMainlineSupportCI P) :
    SeqSelectedTailStaticRouteTypingCI :=
  S.staticProvider.toRouteTyping

/-- Extract coarse selected-tail typing from the static provider. -/
noncomputable def tailCoarseTyping
    {P : StmtNormalPreservationCoreCI}
    (S : SeqCanonicalTailEntryMainlineSupportCI P) :
    SeqTailCoarseTypingAtSelectedNormalCI :=
  S.staticProvider.toCoarseTyping

/-- Extract old tail-return `typed0` support from the static provider. -/
noncomputable def tailReturnTyped0Support
    {P : StmtNormalPreservationCoreCI}
    (S : SeqCanonicalTailEntryMainlineSupportCI P) :
    SeqTailReturnTyped0SupportCI :=
  S.staticProvider.toTailReturnTyped0Support

/--
Boundary-level `seq` support consumed by the case-driver.

This is the important mainline bridge: the recursive tail entry is fixed-static,
so the old selected-route static-alignment obligation is discharged
definitionally.
-/
noncomputable def toBoundaryCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (S : SeqCanonicalTailEntryMainlineSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  S.routeTailBoundary.toBoundaryCoreSupport

end SeqCanonicalTailEntryMainlineSupportCI

/-!
## Constructors from existing infrastructure
-/

/--
Build the mainline support package from existing canonical static source coverage
and fixed-static route tail boundary support.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndFixedRoute
    {P : StmtNormalPreservationCoreCI}
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (B : SeqTailFixedStaticBoundaryAtSelectedRouteCI P) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  { staticProvider :=
      seqTailStaticRouteCertificateProviderCI_of_canonicalSourceCoverage C
    routeTailBoundary := B }

/--
Build the mainline support package from the source-package wrapper and
fixed-static route tail boundary support.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_sourcePackageAndFixedRoute
    {P : StmtNormalPreservationCoreCI}
    (C : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (B : SeqTailFixedStaticBoundaryAtSelectedRouteCI P) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  { staticProvider :=
      seqTailStaticRouteCertificateProviderCI_of_sourcePackage C
    routeTailBoundary := B }

/--
Build the mainline support package from canonical static source coverage plus the
current route-theorem-backed tail entry construction.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndRouteTheoremBacked
    (P : StmtNormalPreservationCoreCI)
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndFixedRoute
    C
    (seqTailFixedStaticBoundaryAtSelectedRouteCI_of_routeTheoremBacked P)

/--
Build boundary-level `seq` support directly from canonical static source coverage
and the current route-theorem-backed tail entry construction.

This is a migration-friendly replacement surface for older constructors that hid
the selected-route/fixed-static split.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_staticSourcesAndRouteTheoremBackedFixed
    (P : StmtNormalPreservationCoreCI)
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndRouteTheoremBacked
    P C).toBoundaryCoreSupport

/--
Build boundary-level `seq` support directly from a source package and
fixed-static route tail boundary support.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_sourcePackageAndFixedRoute
    {P : StmtNormalPreservationCoreCI}
    (C : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (B : SeqTailFixedStaticBoundaryAtSelectedRouteCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqCanonicalTailEntryMainlineSupportCI_of_sourcePackageAndFixedRoute
    C B).toBoundaryCoreSupport

/--
Compatibility alias: the current route-theorem-backed implementation can be
viewed as fixed-static route projection.

Use this when replacing older `seqFunctionBodyClosureBoundaryCoreSupportCI`
constructors in the case-driver path.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_routeTheoremBackedFixedStatic
    (P : StmtNormalPreservationCoreCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_fixedStaticRouteProjection P

end Cpp
