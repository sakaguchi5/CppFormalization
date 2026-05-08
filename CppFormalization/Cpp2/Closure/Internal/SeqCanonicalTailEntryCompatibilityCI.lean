import CppFormalization.Cpp2.Closure.Internal.SeqCanonicalTailEntryDesignCI

namespace Cpp

/-!
# Closure.Internal.SeqCanonicalTailEntryCompatibilityCI

Compatibility bridges for `SeqCanonicalTailEntryDesignCI`.

This file connects the new fixed-static `seq` design to the current route/static
infrastructure.

There are two bridges:

1. existing canonical selected-tail static source coverage gives the new
   `SeqTailStaticRouteCertificateProviderCI`;
2. the current route-projection / normal-preservation / route-adequacy path gives
   `SeqTailFixedStaticBoundaryAtSelectedRouteCI`.

So the new design is not just a documentation layer.  It can be supplied from the
current theorem/projection-backed `seq` route infrastructure.
-/

/-!
## 1. Static route certificate from existing selected-tail source coverage
-/

/--
A fixed-entry static route certificate obtained from canonical selected-tail
source coverage.
-/
noncomputable def seqTailStaticRouteCertificateAtEntryCI_of_canonicalSourceCoverage
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    SeqTailStaticRouteCertificateAtEntryCI hentry :=
  { source := by
      intro hp
      exact C.source hentry hp }

/--
Existing canonical selected-tail static source coverage is exactly the new
static-route certificate provider.

This is the main bridge for the first remaining `seq` question: selected tail
static typing comes from the static source coverage layer.
-/
noncomputable def seqTailStaticRouteCertificateProviderCI_of_canonicalSourceCoverage
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  { certificate := by
      intro Γ σ s t hentry
      exact seqTailStaticRouteCertificateAtEntryCI_of_canonicalSourceCoverage
        C hentry }

/--
The source-package wrapper also gives the new static-route certificate provider.
-/
noncomputable def seqTailStaticRouteCertificateProviderCI_of_sourcePackage
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_canonicalSourceCoverage S.coverage

/--
A convenience theorem-shaped projection: the route typing produced by the new
certificate provider is the existing route typing produced by static sources.
-/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_tailStaticRouteCertificateProvider
    (C : SeqTailStaticRouteCertificateProviderCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  C.toRouteTyping

/-!
## 2. Fixed-static tail boundary from current route-theorem-backed support
-/

/--
The current route-theorem-backed infrastructure gives a fixed-static tail
boundary at the selected route.

The static boundary is not chosen here.  It is the route-projected static
boundary:

`seq_tail_static_boundary_ci_of_head_normal_route_projected hentry hstepHead route`

The remaining fields are the already theorem/projection-backed pieces:

* structural: inherited from the whole sequence boundary;
* dynamic: normal preservation at `route.Θ`;
* adequacy: carried by the selected route payload.
-/
noncomputable def seqTailFixedStaticBoundaryAtSelectedRouteCI_of_routeTheoremBacked
    (P : StmtNormalPreservationCoreCI) :
    SeqTailFixedStaticBoundaryAtSelectedRouteCI P :=
  { boundaryAtRoute := by
      intro Γ σ σ1 s t hentry hstepHead route
      exact
        { structural :=
            seq_tail_structural_boundary_of_entry (Θ := route.Θ) hentry
          dynamic :=
            (seqTailRouteDynamicAlignmentCI_of_normalPreservationCore P).dynamicAtRoute
              hentry hstepHead route
          adequacy :=
            route.tail.support.toBodyAdequacyCI } }

/--
Boundary-level sequence support through the new fixed-static route boundary
surface.

This is a compatibility alias for migration: it factors the current route-backed
support through `SeqTailFixedStaticBoundaryAtSelectedRouteCI`.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_fixedStaticRouteProjection
    (P : StmtNormalPreservationCoreCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqTailFixedStaticBoundaryAtSelectedRouteCI_of_routeTheoremBacked P).toBoundaryCoreSupport

/-!
## 3. Fixed-static selected-payload boundary from an existing static-route payload
-/

/--
An existing static-route payload already supplies the selected-payload
fixed-static recursive boundary.

This is the selected-payload counterpart of
`seqTailFixedStaticBoundaryAtSelectedRouteCI_of_routeTheoremBacked`.
-/
noncomputable def seqSelectedTailFixedStaticBoundaryCI_of_staticRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadStaticRouteCI P) :
    SeqSelectedTailFixedStaticBoundaryCI S.tailStatic P :=
  { boundaryAt := by
      intro Γ σ σ1 s t hentry hstepHead hp
      have hreadyLeft : StmtReadyConcrete Γ σ s :=
        seq_ready_left hentry.dynamic.safe
      have hσ1 : ScopedTypedStateConcrete hp.Θ σ1 :=
        P.preserve hp.hleft hentry.dynamic.state hreadyLeft hstepHead
      have hreadyRight : StmtReadyConcrete hp.Θ σ1 t :=
        seq_ready_right_after_left_normal
          hp.hleft hσ1 hentry.dynamic.safe hstepHead
      exact
        { structural :=
            seq_tail_structural_boundary_of_entry (Θ := hp.Θ) hentry
          dynamic :=
            BodyDynamicBoundary.intro_of_concrete_and_stmtReadyConcrete
              hσ1 hreadyRight
          adequacy :=
            S.tailAdequacy.adequacy hentry hstepHead hp } }

/--
Round-trip an existing static-route payload through the fixed-static selected
tail boundary surface.
-/
noncomputable def seqSelectedHeadNormalRoutePayloadStaticRouteCI_of_fixedStaticRoundTrip
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadStaticRouteCI P) :
    SeqSelectedHeadNormalRoutePayloadStaticRouteCI P :=
  (seqSelectedTailFixedStaticBoundaryCI_of_staticRoutePayload S).toStaticRoutePayload

/--
Boundary support from an existing static-route payload, factored through the
fixed-static selected-tail boundary design.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_staticRoutePayload_fixedStatic
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadStaticRouteCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_staticRoutePayload
    (seqSelectedHeadNormalRoutePayloadStaticRouteCI_of_fixedStaticRoundTrip S)

/-!
## 4. Package-level constructors for the new design
-/

/--
Build the natural canonical tail-entry design from a static certificate provider
and a fixed-static selected-tail boundary provider.
-/
noncomputable def seqCanonicalTailEntryDesignCI_of_staticProviderAndFixedTail
    {P : StmtNormalPreservationCoreCI}
    (C : SeqTailStaticRouteCertificateProviderCI)
    (B : SeqSelectedTailFixedStaticBoundaryCI C.toRouteTyping P) :
    SeqCanonicalTailEntryDesignCI P :=
  { staticProvider := C
    tailBoundary := B }

/--
Build the natural canonical tail-entry design from existing canonical static
source coverage and a fixed-static selected-tail boundary for the induced route
typing.
-/
noncomputable def seqCanonicalTailEntryDesignCI_of_canonicalSourceCoverageAndFixedTail
    {P : StmtNormalPreservationCoreCI}
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (B :
      SeqSelectedTailFixedStaticBoundaryCI
        (seqTailStaticRouteCertificateProviderCI_of_canonicalSourceCoverage C).toRouteTyping
        P) :
    SeqCanonicalTailEntryDesignCI P :=
  seqCanonicalTailEntryDesignCI_of_staticProviderAndFixedTail
    (seqTailStaticRouteCertificateProviderCI_of_canonicalSourceCoverage C)
    B

end Cpp
