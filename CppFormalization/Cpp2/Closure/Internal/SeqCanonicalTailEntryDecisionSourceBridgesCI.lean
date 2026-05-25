import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverCanonicalSeqWhileReentryCI

namespace Cpp

/-!
# Closure.Internal.SeqCanonicalTailEntryDecisionSourceBridgesCI

Decision-source bridges for the canonical fixed-static `seq` design.

The current canonical case-driver entry can consume
`SeqCanonicalSelectedTailStaticSourceCoverageCI`.  That is already a static
source coverage object, but it is still slightly too high-level as a mainline
dependency.

This file pushes the entry one layer lower:

* normal/tail-return decision-source coverage produces the static route
  certificate provider;
* return typing plus coarse selected-tail typing produces the static route
  certificate provider;
* those lower static certificates feed the canonical fixed-static `seq`
  case-driver entry.

C++ reading: the static entry of `t` in `s; t` is not a semantic or recursive
assumption.  It is reconstructed from the static provenance of the sequence
typing: after the selected normal exit of `s`, the tail `t` is typed in the
selected post-environment.
-/

/-!
## 1. Static certificate providers from lower decision-source layers
-/

/--
Decision-source coverage gives the canonical fixed-static static-route
certificate provider.

This is the direct lower-static bridge from selected normal/tail-return
decision provenance to the new static-provider surface.
-/
noncomputable def seqTailStaticRouteCertificateProviderCI_of_decisionSources
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_canonicalSourceCoverage
    (seqCanonicalSelectedTailStaticSourceCoverageCI_of_decisionSources C)

/--
Split return-typing decision coverage plus separated tail-return `typed0`
support gives the new static-route certificate provider.
-/
noncomputable def seqTailStaticRouteCertificateProviderCI_of_returnTypingAndTyped0
    (T0 : SeqTailReturnTyped0SupportCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_decisionSources
    (seqSelectedTailStaticDecisionSourceCoverageCI_of_returnTypingAndTyped0 T0 C)

/--
Split return-typing decision coverage plus lower selected-tail coarse typing
gives the new static-route certificate provider.

This is the important bridge for the current target: `typed0` is not supplied by
a return-channel decision.  It is supplied by the selected-tail coarse typing
fact.
-/
noncomputable def seqTailStaticRouteCertificateProviderCI_of_returnTypingAndTailCoarseTyping
    (T : SeqTailCoarseTypingAtSelectedNormalCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_returnTypingAndTyped0
    (seqTailReturnTyped0SupportCI_of_tailCoarseTyping T)
    C

/--
Aligned selected-tail static sources can also supply the separated tail-return
`typed0` support, hence the static-route certificate provider.
-/
noncomputable def seqTailStaticRouteCertificateProviderCI_of_returnTypingAndAlignedStaticSources
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_returnTypingAndTyped0
    (seqTailReturnTyped0SupportCI_of_alignedStaticSources S)
    C

/--
Old selected-tail typing source coverage gives coarse selected-tail typing, hence
the static-route certificate provider.
-/
noncomputable def seqTailStaticRouteCertificateProviderCI_of_returnTypingAndOldTypingSources
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_returnTypingAndTailCoarseTyping
    (seqTailCoarseTypingAtSelectedNormalCI_of_oldTypingSources T)
    C

/-!
## 2. Canonical mainline support from lower static providers
-/

/--
Build canonical fixed-static `seq` mainline support from an already-built static
certificate provider and the current route-theorem-backed fixed-static tail
entry.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_staticProviderAndRouteTheoremBacked
    (P : StmtNormalPreservationCoreCI)
    (S : SeqTailStaticRouteCertificateProviderCI) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  { staticProvider := S
    routeTailBoundary :=
      seqTailFixedStaticBoundaryAtSelectedRouteCI_of_routeTheoremBacked P }

/--
Build canonical fixed-static `seq` mainline support from decision-source
coverage.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_decisionSourcesAndRouteTheoremBacked
    (P : StmtNormalPreservationCoreCI)
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  seqCanonicalTailEntryMainlineSupportCI_of_staticProviderAndRouteTheoremBacked
    P
    (seqTailStaticRouteCertificateProviderCI_of_decisionSources C)

/--
Build canonical fixed-static `seq` mainline support from split return-typing
coverage plus lower selected-tail coarse typing.
-/
noncomputable def seqCanonicalTailEntryMainlineSupportCI_of_returnTypingAndTailCoarseTyping
    (P : StmtNormalPreservationCoreCI)
    (T : SeqTailCoarseTypingAtSelectedNormalCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqCanonicalTailEntryMainlineSupportCI P :=
  seqCanonicalTailEntryMainlineSupportCI_of_staticProviderAndRouteTheoremBacked
    P
    (seqTailStaticRouteCertificateProviderCI_of_returnTypingAndTailCoarseTyping T C)

/--
Boundary-level `seq` support from decision-source coverage, routed through the
canonical fixed-static design.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_decisionSourcesAndRouteTheoremBackedFixed
    (P : StmtNormalPreservationCoreCI)
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqCanonicalTailEntryMainlineSupportCI_of_decisionSourcesAndRouteTheoremBacked
    P C).toBoundaryCoreSupport

/--
Boundary-level `seq` support from split return-typing coverage plus lower
selected-tail coarse typing.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_returnTypingAndTailCoarseTypingFixed
    (P : StmtNormalPreservationCoreCI)
    (T : SeqTailCoarseTypingAtSelectedNormalCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  (seqCanonicalTailEntryMainlineSupportCI_of_returnTypingAndTailCoarseTyping
    P T C).toBoundaryCoreSupport

/-!
## 3. Canonical case-driver support from lower static providers
-/

/--
Canonical case-driver support from a static certificate provider and the current
`whileReentry` implementation.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_staticProviderAndWhileReentry
    (S : SeqTailStaticRouteCertificateProviderCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  let Pold := stmtNormalPreservationProviderCI_of_whileReentry
  let P := Pold.toCore
  { P := P
    seq := seqCanonicalTailEntryMainlineSupportCI_of_staticProviderAndRouteTheoremBacked P S
    whileSupport := whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry
    whileInvariant := W }

/--
Canonical case-driver support from decision-source coverage and the current
`whileReentry` implementation.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_decisionSourcesAndWhileReentry
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  functionBodyCanonicalSeqCaseDriverSupportCI_of_staticProviderAndWhileReentry
    (seqTailStaticRouteCertificateProviderCI_of_decisionSources C)
    W

/--
Canonical case-driver support from split return-typing coverage plus lower
selected-tail coarse typing.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_returnTypingAndTailCoarseTyping
    (T : SeqTailCoarseTypingAtSelectedNormalCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  functionBodyCanonicalSeqCaseDriverSupportCI_of_staticProviderAndWhileReentry
    (seqTailStaticRouteCertificateProviderCI_of_returnTypingAndTailCoarseTyping T C)
    W

/-!
## 4. More aggressive case-driver entry theorems
-/

/--
Case-driver body using canonical fixed-static `seq` support supplied directly
from decision-source coverage.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_decisionSources_canonicalSeq
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyCanonicalSeqCaseDriverSupportCI_of_decisionSourcesAndWhileReentry
    C W).bodyClosure IH hfrag hentry

/--
`BodyReadyCI` wrapper for the decision-source canonical `seq` case-driver body.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_decisionSources_canonicalSeq
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_decisionSources_canonicalSeq
    C W IH hfrag hentry.toClosureBoundary

/--
Case-driver body using canonical fixed-static `seq` support supplied from split
return-typing decision coverage plus lower selected-tail coarse typing.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingTailCoarse_canonicalSeq
    (T : SeqTailCoarseTypingAtSelectedNormalCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyCanonicalSeqCaseDriverSupportCI_of_returnTypingAndTailCoarseTyping
    T C W).bodyClosure IH hfrag hentry

/--
`BodyReadyCI` wrapper for the split return-typing / coarse-tail canonical `seq`
case-driver body.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_returnTypingTailCoarse_canonicalSeq
    (T : SeqTailCoarseTypingAtSelectedNormalCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingTailCoarse_canonicalSeq
    T C W IH hfrag hentry.toClosureBoundary

end Cpp
