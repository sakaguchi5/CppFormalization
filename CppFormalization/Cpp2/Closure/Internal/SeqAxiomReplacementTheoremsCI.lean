import CppFormalization.Cpp2.Closure.Internal.SeqCanonicalTailEntryCoarseTypingEliminationCI

namespace Cpp

/-!
# Closure.Internal.SeqAxiomReplacementTheoremsCI

Theorem/def-backed replacements for the old axiom-shaped `seq` obligations.

This file is intentionally aggressive.  It does not merely add another design
layer; it names the old axiom-shaped responsibilities as theorem-backed
replacement surfaces.

What can be replaced now:

* selected-tail static source coverage;
* selected-tail coarse typing;
* selected-tail static route certificate provider;
* left adequacy residual;
* selected-route tail boundary alignment;
* boundary-level `seq` support;
* case-driver `seq` support.

What is not replaced here:

* the global recursive hypothesis
  `body_closure_ci_function_body_global_recursion`.

That one is not a C++ semantic contract and not a local `seq` obligation.  It is
a proof-architecture/global-recursion issue for the constructor-level driver,
especially because `while` recurs on the same syntax.
-/

/-!
## 1. Static-source and coarse-typing replacements
-/

/--
Theorem-backed replacement for an axiom-shaped selected-tail static source
coverage assumption, when a source package is available.

This is a `def` because the source package already stores the coverage.
-/
noncomputable def seq_selected_tail_static_source_coverage_def
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqCanonicalSelectedTailStaticSourceCoverageCI :=
  S.coverage

/--
Theorem-backed replacement for `SeqTailCoarseTypingAtSelectedNormalCI` from a
full selected-tail static source package.
-/
noncomputable def seq_tail_coarse_typing_at_selected_normal_def
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqTailCoarseTypingAtSelectedNormalCI :=
  seqTailCoarseTypingAtSelectedNormalCI_of_canonicalStaticSources
    S.coverage

/--
Theorem-backed replacement for old tail-return `typed0` support from a full
selected-tail static source package.
-/
noncomputable def seq_tail_return_typed0_support_def
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqTailReturnTyped0SupportCI :=
  seqTailReturnTyped0SupportCI_of_canonicalStaticSources
    S.coverage

/--
Theorem-backed replacement for the selected-tail static route certificate
provider from a full selected-tail static source package.
-/
noncomputable def seq_tail_static_route_certificate_provider_def
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_sourcePackage S

/--
Theorem-backed replacement for selected-tail static route typing from a full
selected-tail static source package.
-/
noncomputable def seq_selected_tail_static_route_typing_def
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  (seq_tail_static_route_certificate_provider_def S).toRouteTyping

/-!
## 2. Lower-static replacements that do not expose coarse typing
-/

/--
Theorem-backed replacement for the static certificate provider from old typing
source coverage plus return-typing decision coverage.

This is the non-axiom route that derives the coarse selected-tail typing
internally.
-/
noncomputable def seq_tail_static_route_certificate_provider_of_oldTyping_def
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_returnTypingAndOldTypingSources
    T C

/--
Theorem-backed replacement for the static certificate provider from aligned
static sources plus return-typing decision coverage.
-/
noncomputable def seq_tail_static_route_certificate_provider_of_alignedStatic_def
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_returnTypingAndAlignedStaticSources
    S C

/--
Theorem-backed replacement for the static certificate provider from decision
source coverage.
-/
noncomputable def seq_tail_static_route_certificate_provider_of_decisionSources_def
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI) :
    SeqTailStaticRouteCertificateProviderCI :=
  seqTailStaticRouteCertificateProviderCI_of_decisionSources C

/-!
## 3. Semantic/projection replacements
-/

/--
Theorem-backed replacement for the old left-adequacy residual.

Left adequacy is not a fresh assumption: it is the adequacy field of the left
boundary extracted from the sequence entry.
-/
noncomputable def seq_left_adequacy_residual_def
    (P : StmtNormalPreservationCoreCI) :
    SeqLeftAdequacyResidualCoreSupportCI P :=
  seqLeftAdequacyResidualCoreSupportCI_of_leftEntryBoundary P

/--
Theorem-backed replacement for the old selected-route tail-boundary-alignment
axiom shape.

The fixed-static route boundary supplies the ordinary selected-route boundary
with static equality by `rfl`.
-/
noncomputable def seq_tail_boundary_for_selected_route_def
    (P : StmtNormalPreservationCoreCI) :
    SeqTailBoundaryForSelectedRouteCoreSupportCI P :=
  (seqTailFixedStaticBoundaryAtSelectedRouteCI_of_routeTheoremBacked P).toBoundaryForSelectedRoute

/--
Theorem-backed replacement for selected-route tail adequacy.

The adequacy is projected from the fixed-static selected-route tail boundary.
-/
noncomputable def seq_tail_adequacy_for_selected_route_def
    (P : StmtNormalPreservationCoreCI) :
    SeqTailAdequacyForSelectedRouteCoreSupportCI P :=
  (seq_tail_boundary_for_selected_route_def P).toSelectedRouteAdequacy

/-!
## 4. Boundary-level `seq` replacement surfaces
-/

/--
Boundary-level `seq` support from a full selected-tail static source package,
through the canonical fixed-static design.

This is the clean replacement surface for older route/static payload axioms in
the sequence path.
-/
noncomputable def seq_function_body_closure_boundary_core_support_def
    (P : StmtNormalPreservationCoreCI)
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_sourcePackageRouteTheoremBackedFixed
    P S

/--
Boundary-level `seq` support from old typing source coverage plus return-typing
decision coverage, deriving coarse typing internally.
-/
noncomputable def seq_function_body_closure_boundary_core_support_of_oldTyping_def
    (P : StmtNormalPreservationCoreCI)
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_returnTypingAndOldTypingSourcesFixed
    P T C

/--
Boundary-level `seq` support from aligned static sources plus return-typing
decision coverage, deriving tail-return typed0 internally.
-/
noncomputable def seq_function_body_closure_boundary_core_support_of_alignedStatic_def
    (P : StmtNormalPreservationCoreCI)
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_returnTypingAndAlignedStaticSourcesFixed
    P S C

/--
Boundary-level `seq` support from decision-source coverage.
-/
noncomputable def seq_function_body_closure_boundary_core_support_of_decisionSources_def
    (P : StmtNormalPreservationCoreCI)
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_decisionSourcesAndRouteTheoremBackedFixed
    P C

/-!
## 5. Case-driver replacement surfaces
-/

/--
Case-driver theorem-backed replacement using a full selected-tail static source
package.

This removes the old axiom-shaped `seq` static/coarse obligations from the
case-driver surface.
-/
theorem body_closure_case_driver_sourcePackage_theorem
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_sourcePackage_canonicalSeq
    S W IH hfrag hentry

/--
Case-driver theorem-backed replacement using old typing source coverage plus
return-typing decision coverage.
-/
theorem body_closure_case_driver_oldTyping_theorem
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingOldTyping_canonicalSeq
    T C W IH hfrag hentry

/--
Case-driver theorem-backed replacement using aligned static sources plus
return-typing decision coverage.
-/
theorem body_closure_case_driver_alignedStatic_theorem
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_returnTypingAlignedStatic_canonicalSeq
    S C W IH hfrag hentry

/--
Case-driver theorem-backed replacement using decision-source coverage.
-/
theorem body_closure_case_driver_decisionSources_theorem
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_decisionSources_canonicalSeq
    C W IH hfrag hentry

end Cpp
