import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCanonicalSeqSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverCanonicalSeqWhileReentryCI

Canonical fixed-static `seq` support from the current `whileReentry` entry.

This file is intentionally more mainline-facing than the previous compatibility
layers.

The old compatibility constructor

`boundarySeqAndWhileCoreSupports_of_whileReentry`

returns only the generic boundary-core `seq` support.  That hides the fixed-static
tail-entry design.

This file keeps the same practical source of preservation/while support
(`WhileReentryReadyProvider`), but makes the `seq` dependency canonical:

* normal preservation core comes from `stmtNormalPreservationProviderCI_of_whileReentry`;
* while closure support comes from `whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry`;
* seq support is built as `SeqCanonicalTailEntryMainlineSupportCI`, using an
  explicit static source coverage certificate.

C++ reading: `whileReentry` is still allowed to be the current way of obtaining
normal preservation and while closure support, but `seq` itself now enters the
tail through a fixed selected static boundary.
-/

/--
Canonical fixed-static `seq` support plus while support, built from the current
`whileReentry` provider and an explicit selected-tail static source coverage
certificate.

This is the canonical counterpart of
`boundarySeqAndWhileCoreSupports_of_whileReentry`.
-/
noncomputable def canonicalSeqAndWhileCoreSupports_of_staticSourcesAndWhileReentry
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI):
    let P := (stmtNormalPreservationProviderCI_of_whileReentry ).toCore
    SeqCanonicalTailEntryMainlineSupportCI P × WhileCurrentBoundaryClosureCoreSupportCI :=
  let Pold := stmtNormalPreservationProviderCI_of_whileReentry
  let P := Pold.toCore
  (seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndRouteTheoremBacked P C,
   whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry )

/--
Build the canonical case-driver support package from selected-tail static source
coverage and the current `whileReentry` provider.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_staticSourcesAndWhileReentry
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  let Pold := stmtNormalPreservationProviderCI_of_whileReentry
  let P := Pold.toCore
  { P := P
    seq := seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndRouteTheoremBacked P C
    whileSupport := whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry
    whileInvariant := W }

/--
Constructor-level case-driver body from the current `whileReentry` provider, but
with canonical fixed-static `seq` support made explicit.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeq_whileReentry
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyCanonicalSeqCaseDriverSupportCI_of_staticSourcesAndWhileReentry
    C  W).bodyClosure IH hfrag hentry

/--
`BodyReadyCI` wrapper for the canonical fixed-static `seq` / `whileReentry`
case-driver body.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeq_whileReentry
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeq_whileReentry
    C W IH hfrag hentry.toClosureBoundary

/-!
## Pair-level compatibility projections

These definitions are deliberately named as replacements for the older generic
support pair.  They make it easy to migrate callers one at a time.
-/

/--
Project the canonical support pair to the older generic boundary-core pair.

This keeps old consumers working while allowing new consumers to keep the richer
canonical `seq` support visible.
-/
noncomputable def boundarySeqAndWhileCoreSupports_of_canonicalSeqAndWhile
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P × WhileCurrentBoundaryClosureCoreSupportCI :=
  (Seq.toBoundaryCoreSupport, Wh)

/--
The old generic support pair, but routed through the canonical fixed-static `seq`
construction first.

Use this as a drop-in migration bridge when a caller still expects the old pair
shape.
-/
noncomputable def boundarySeqAndWhileCoreSupports_of_staticSourcesAndWhileReentry_fixedStatic
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI):
    let P := (stmtNormalPreservationProviderCI_of_whileReentry ).toCore
    SeqFunctionBodyClosureBoundaryCoreSupportCI P × WhileCurrentBoundaryClosureCoreSupportCI :=
  let pair := canonicalSeqAndWhileCoreSupports_of_staticSourcesAndWhileReentry C
  boundarySeqAndWhileCoreSupports_of_canonicalSeqAndWhile pair.1 pair.2

/--
A direct boundary-core-support case-driver theorem using the fixed-static route,
for callers that are not yet ready to depend on
`FunctionBodyCanonicalSeqCaseDriverSupportCI`.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_boundaryCoreSupport_fixedStaticWhileReentry
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  let Pold := stmtNormalPreservationProviderCI_of_whileReentry
  let P := Pold.toCore
  let Seq := seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndRouteTheoremBacked P C
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_boundaryCoreSupport
    P
    Seq.toBoundaryCoreSupport
    (whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry )
    W
    IH
    hfrag
    hentry

end Cpp
