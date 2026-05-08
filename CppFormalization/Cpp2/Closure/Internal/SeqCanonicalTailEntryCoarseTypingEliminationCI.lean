import CppFormalization.Cpp2.Closure.Internal.SeqCanonicalTailEntryDecisionSourceBridgesCI

namespace Cpp

/-!
# Closure.Internal.SeqCanonicalTailEntryCoarseTypingEliminationCI

More aggressive lower-static entry points for the canonical fixed-static `seq`
design.

`SeqCanonicalTailEntryDecisionSourceBridgesCI` still exposes an important but
intermediate route:

`SeqTailCoarseTypingAtSelectedNormalCI`
+
`SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI`
→ canonical fixed-static `seq` support.

This file pushes one step further.  It provides mainline/case-driver entry
points where the coarse selected-tail typing is not a separate argument.  Instead
it is produced from one of the lower static sources:

* old selected-tail typing source coverage;
* aligned selected-tail static source coverage;
* a full selected-tail static source package.

C++ reading: after the selected normal exit of `s` in `s; t`, the fact that `t`
is statically readable at the selected post-environment should be supplied by
the static typing/source layer.  The function-body case-driver should not need
to mention that coarse fact as an independent semantic obligation.
-/

/-!
## 1. Mainline support without an explicit coarse-typing argument
-/

/--
Canonical fixed-static `seq` mainline support from split return-typing decision
coverage plus old selected-tail typing source coverage.

This removes `SeqTailCoarseTypingAtSelectedNormalCI` from the surface by deriving
it from `SeqTailOldTypingSourceCoverageCI`.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_returnTypingAndOldTypingSources
    (P : StmtNormalPreservationCoreCI)
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  seqCanonicalTailEntryMainlineSupportCI_of_staticProviderAndRouteTheoremBacked
    P
    (seqTailStaticRouteCertificateProviderCI_of_returnTypingAndOldTypingSources
      T C)

/--
Canonical fixed-static `seq` mainline support from split return-typing decision
coverage plus aligned selected-tail static sources.

Here the separated tail-return `typed0` support is projected from the aligned
static source itself.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_returnTypingAndAlignedStaticSources
    (P : StmtNormalPreservationCoreCI)
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  seqCanonicalTailEntryMainlineSupportCI_of_staticProviderAndRouteTheoremBacked
    P
    (seqTailStaticRouteCertificateProviderCI_of_returnTypingAndAlignedStaticSources
      S C)

/--
Canonical fixed-static `seq` mainline support from a full selected-tail static
source package.

This is the cleanest static-source entry: the package already contains canonical
source coverage, so it immediately gives the static certificate provider.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_sourcePackageAndRouteTheoremBacked
    (P : StmtNormalPreservationCoreCI)
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  seqCanonicalTailEntryMainlineSupportCI_of_staticProviderAndRouteTheoremBacked
    P
    (seqTailStaticRouteCertificateProviderCI_of_sourcePackage S)

/-!
## 2. Boundary-core support without an explicit coarse-typing argument
-/

/--
Boundary-level `seq` support from old selected-tail typing source coverage.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_returnTypingAndOldTypingSourcesFixed
    (P : StmtNormalPreservationCoreCI)
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqCanonicalTailEntryMainlineSupportCI_of_returnTypingAndOldTypingSources
    P T C).toBoundaryCoreSupport

/--
Boundary-level `seq` support from aligned selected-tail static sources.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_returnTypingAndAlignedStaticSourcesFixed
    (P : StmtNormalPreservationCoreCI)
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqCanonicalTailEntryMainlineSupportCI_of_returnTypingAndAlignedStaticSources
    P S C).toBoundaryCoreSupport

/--
Boundary-level `seq` support from a full static source package.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_sourcePackageRouteTheoremBackedFixed
    (P : StmtNormalPreservationCoreCI)
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqCanonicalTailEntryMainlineSupportCI_of_sourcePackageAndRouteTheoremBacked
    P S).toBoundaryCoreSupport

/-!
## 3. Canonical case-driver support without an explicit coarse-typing argument
-/

/--
Canonical case-driver support from old selected-tail typing source coverage and
the current `whileReentry` implementation.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_returnTypingAndOldTypingSources
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  functionBodyCanonicalSeqCaseDriverSupportCI_of_staticProviderAndWhileReentry
    (seqTailStaticRouteCertificateProviderCI_of_returnTypingAndOldTypingSources
      T C)
    mkWhileReentry
    W

/--
Canonical case-driver support from aligned selected-tail static sources and the
current `whileReentry` implementation.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_returnTypingAndAlignedStaticSources
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  functionBodyCanonicalSeqCaseDriverSupportCI_of_staticProviderAndWhileReentry
    (seqTailStaticRouteCertificateProviderCI_of_returnTypingAndAlignedStaticSources
      S C)
    mkWhileReentry
    W

/--
Canonical case-driver support from a full selected-tail static source package and
the current `whileReentry` implementation.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_sourcePackage
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  functionBodyCanonicalSeqCaseDriverSupportCI_of_staticProviderAndWhileReentry
    (seqTailStaticRouteCertificateProviderCI_of_sourcePackage S)
    mkWhileReentry
    W

/-!
## 4. Case-driver entry theorems without an explicit coarse-typing argument
-/

/--
Case-driver body from old selected-tail typing sources.

This is the lower-static replacement for the route that explicitly asked for
`SeqTailCoarseTypingAtSelectedNormalCI`.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingOldTyping_canonicalSeq
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyCanonicalSeqCaseDriverSupportCI_of_returnTypingAndOldTypingSources
    T C mkWhileReentry W).bodyClosure IH hfrag hentry

/--
`BodyReadyCI` wrapper for the old-typing-source canonical case-driver body.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_returnTypingOldTyping_canonicalSeq
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingOldTyping_canonicalSeq
    T C mkWhileReentry W IH hfrag hentry.toClosureBoundary

/--
Case-driver body from aligned selected-tail static sources.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingAlignedStatic_canonicalSeq
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyCanonicalSeqCaseDriverSupportCI_of_returnTypingAndAlignedStaticSources
    S C mkWhileReentry W).bodyClosure IH hfrag hentry

/--
`BodyReadyCI` wrapper for the aligned-static-source canonical case-driver body.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_returnTypingAlignedStatic_canonicalSeq
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingAlignedStatic_canonicalSeq
    S C mkWhileReentry W IH hfrag hentry.toClosureBoundary

/--
Case-driver body from a full selected-tail static source package.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_sourcePackage_canonicalSeq
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyCanonicalSeqCaseDriverSupportCI_of_sourcePackage
    S mkWhileReentry W).bodyClosure IH hfrag hentry

/--
`BodyReadyCI` wrapper for the source-package canonical case-driver body.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_sourcePackage_canonicalSeq
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (mkWhileReentry : WhileReentryReadyProvider)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_sourcePackage_canonicalSeq
    S mkWhileReentry W IH hfrag hentry.toClosureBoundary

end Cpp
