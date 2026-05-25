import CppFormalization.Cpp2.Closure.Internal.CurrentShellCI
import CppFormalization.Cpp2.Closure.Internal.SeqAxiomReplacementTheoremsCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyClosureCanonicalSeqGlobalShellCI

Canonical fixed-static `seq` closure through the remaining global recursion shell.

This file makes the current status explicit:

* `seq` local obligations are supplied by theorem/def-backed replacement
  surfaces from `SeqAxiomReplacementTheoremsCI`;
* the only remaining shell used here is
  `body_closure_ci_function_body_global_recursion : FunctionBodyCaseDriverIH`.

In other words, this file does not pretend that the global recursion shell is
solved.  It isolates it.

C++ reading:
The sequence-specific question “after `s` falls through, does `t` enter through
the correct selected static boundary?” is no longer a global axiom here.  It is
handled by the canonical fixed-static `seq` support.  The remaining assumption is
only the proof-architecture principle that the constructor-level case-driver may
be used recursively, including for while tails.
-/

/-!
## 1. Boundary-entry master wrappers through the remaining global shell
-/

/--
Master closure wrapper using a full selected-tail static source package.

All `seq` static/coarse/tail-boundary obligations are supplied by
`body_closure_case_driver_sourcePackage_theorem`; the only remaining shell is the
global recursion hypothesis.
-/
theorem body_closure_ci_function_body_progress_or_diverges_sourcePackage_globalShell
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_case_driver_sourcePackage_theorem
    S
    W
    body_closure_ci_function_body_global_recursion
    hfrag
    hentry

/--
Master closure wrapper using old selected-tail typing sources plus return-typing
decision coverage.

This internally derives the coarse selected-tail typing and uses the
fixed-static `seq` design.
-/
theorem body_closure_ci_function_body_progress_or_diverges_oldTyping_globalShell
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_case_driver_oldTyping_theorem
    T
    C
    W
    body_closure_ci_function_body_global_recursion
    hfrag
    hentry

/--
Master closure wrapper using aligned selected-tail static sources plus
return-typing decision coverage.
-/
theorem body_closure_ci_function_body_progress_or_diverges_alignedStatic_globalShell
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_case_driver_alignedStatic_theorem
    S
    C
    W
    body_closure_ci_function_body_global_recursion
    hfrag
    hentry

/--
Master closure wrapper using decision-source coverage.
-/
theorem body_closure_ci_function_body_progress_or_diverges_decisionSources_globalShell
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_case_driver_decisionSources_theorem
    C
    W
    body_closure_ci_function_body_global_recursion
    hfrag
    hentry

/-!
## 2. BodyReady wrappers through the remaining global shell
-/

/--
`BodyReadyCI` wrapper for the source-package global-shell theorem.
-/
theorem body_ready_ci_function_body_progress_or_diverges_sourcePackage_globalShell
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_sourcePackage_globalShell
    S W hfrag hentry.toClosureBoundary

/--
`BodyReadyCI` wrapper for the old-typing-source global-shell theorem.
-/
theorem body_ready_ci_function_body_progress_or_diverges_oldTyping_globalShell
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_oldTyping_globalShell
    T C W hfrag hentry.toClosureBoundary

/--
`BodyReadyCI` wrapper for the aligned-static global-shell theorem.
-/
theorem body_ready_ci_function_body_progress_or_diverges_alignedStatic_globalShell
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_alignedStatic_globalShell
    S C W hfrag hentry.toClosureBoundary

/--
`BodyReadyCI` wrapper for the decision-source global-shell theorem.
-/
theorem body_ready_ci_function_body_progress_or_diverges_decisionSources_globalShell
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_decisionSources_globalShell
    C W hfrag hentry.toClosureBoundary

/-!
## 3. Named status theorem

This theorem is intentionally boring: it states the project status in the type
system.  With a source package, while reentry, and a while invariant provider,
function-body closure follows from the single remaining global recursion shell.
-/

/--
Status theorem: canonical fixed-static `seq` has been removed from the shell
debt.  The only shell consumed by this theorem is
`body_closure_ci_function_body_global_recursion`.
-/
theorem canonicalSeq_closure_reduces_to_global_recursion_shell
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_sourcePackage_globalShell
    S W hfrag hentry

end Cpp
