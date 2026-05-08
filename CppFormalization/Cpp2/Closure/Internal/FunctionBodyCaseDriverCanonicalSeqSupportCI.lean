import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverBoundaryCoreSupportCI
import CppFormalization.Cpp2.Closure.Internal.SeqCanonicalTailEntryMainlineSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverCanonicalSeqSupportCI

A more aggressive mainline surface for the fixed-static `seq` design.

The earlier compatibility files proved that the fixed-static design can be
connected to the current route-theorem-backed implementation.  This file moves
the new design one step closer to the real case-driver surface:

* the `seq` dependency of the case-driver is now
  `SeqCanonicalTailEntryMainlineSupportCI P`;
* the ordinary boundary-core support is obtained only as a projection;
* route-theorem-backed compatibility is still available, but is no longer the
  name of the main theorem.

C++ reading: the function-body case driver treats `s; t` by first selecting the
static entry for `t` from the normal exit of `s`, and then entering `t` through
that fixed static entry.  This prevents the recursive tail call from silently
changing the static profile.
-/

/--
Canonical sequence closure surface induced by the fixed-static tail-entry design.

This is the `seq` theorem name that should be used by new code.  It exposes the
new design at the public surface and only then forgets to the existing
boundary-core support.
-/
theorem seq_function_body_closure_boundary_ci_canonicalTailEntry
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyClosureBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) :=
  seq_function_body_closure_boundary_ci_of_boundaryCoreSupport
    Seq.toBoundaryCoreSupport
    hentry
    leftClosure
    tailClosure

/--
Constructor-level case-driver body whose `seq` dependency is the canonical
fixed-static tail-entry support, not the older generic boundary-core support.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_boundaryCoreSupport
    P
    Seq.toBoundaryCoreSupport
    Wh
    W
    IH
    hfrag
    hentry

/--
`BodyReadyCI` wrapper for the canonical fixed-static `seq` case-driver body.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport
    P Seq Wh W IH hfrag hentry.toClosureBoundary

/-!
## Packaged driver dependency

This package is intentionally opinionated: the canonical `seq` dependency is
fixed-static, while `while` remains its current cleaned boundary-closure support
plus the explicit backedge invariant provider.
-/

/--
Canonical case-driver support package.

Compared with the older `P + SeqFunctionBodyClosureBoundaryCoreSupportCI P + Wh
+ W` shape, this package keeps the richer fixed-static `seq` support visible.
-/
structure FunctionBodyCanonicalSeqCaseDriverSupportCI : Type where
  P : StmtNormalPreservationCoreCI
  seq : SeqCanonicalTailEntryMainlineSupportCI P
  whileSupport : WhileCurrentBoundaryClosureCoreSupportCI
  whileInvariant : FunctionBodyWhileBackedgeInvariantCoreProviderCI

namespace FunctionBodyCanonicalSeqCaseDriverSupportCI

/-- Forget the canonical package to the older boundary-core `seq` support. -/
noncomputable def seqBoundaryCore
    (S : FunctionBodyCanonicalSeqCaseDriverSupportCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI S.P :=
  S.seq.toBoundaryCoreSupport

/-- Run the case-driver body from the canonical fixed-static `seq` package. -/
theorem bodyClosure
    (S : FunctionBodyCanonicalSeqCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_canonicalSeqSupport
    S.P
    S.seq
    S.whileSupport
    S.whileInvariant
    IH
    hfrag
    hentry

/-- `BodyReadyCI` wrapper for the packaged canonical driver body. -/
theorem bodyReady
    (S : FunctionBodyCanonicalSeqCaseDriverSupportCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  S.bodyClosure IH hfrag hentry.toClosureBoundary

end FunctionBodyCanonicalSeqCaseDriverSupportCI

/-!
## Aggressive constructors from existing infrastructure

These constructors make the new fixed-static surface easy to use immediately.
They do not hide the new design; rather, they build it from the currently
available theorem/projection-backed pieces.
-/

/--
Build the canonical case-driver support package from explicit canonical `seq`
support plus the current while supports.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_components
    (P : StmtNormalPreservationCoreCI)
    (Seq : SeqCanonicalTailEntryMainlineSupportCI P)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  { P := P
    seq := Seq
    whileSupport := Wh
    whileInvariant := W }

/--
Build the canonical case-driver support package from static source coverage and
the route-theorem-backed fixed-static tail entry.
-/
noncomputable def functionBodyCanonicalSeqCaseDriverSupportCI_of_staticSourcesAndRouteTheoremBacked
    (P : StmtNormalPreservationCoreCI)
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI) :
    FunctionBodyCanonicalSeqCaseDriverSupportCI :=
  functionBodyCanonicalSeqCaseDriverSupportCI_of_components
    P
    (seqCanonicalTailEntryMainlineSupportCI_of_staticSourcesAndRouteTheoremBacked P C)
    Wh
    W

/--
Case-driver body from static source coverage plus route-theorem-backed
fixed-static tail entry.

This is the aggressive migration theorem: it uses the new canonical `seq`
surface directly, while still allowing the current route-backed implementation
to supply the fixed-static tail boundary.
-/
theorem body_closure_ci_function_body_progress_or_diverges_case_driver_body_staticSources_routeTheoremBackedSeq
    (P : StmtNormalPreservationCoreCI)
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyClosureBoundaryCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  (functionBodyCanonicalSeqCaseDriverSupportCI_of_staticSourcesAndRouteTheoremBacked
    P C Wh W).bodyClosure IH hfrag hentry

/--
`BodyReadyCI` wrapper for the aggressive migration theorem.
-/
theorem body_ready_ci_function_body_progress_or_diverges_case_driver_body_staticSources_routeTheoremBackedSeq
    (P : StmtNormalPreservationCoreCI)
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI)
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (hfrag : CoreBigStepFragment st)
    (hentry : BodyReadyCI Γ σ st) :
    FunctionBodyCaseDriverResult σ st :=
  body_closure_ci_function_body_progress_or_diverges_case_driver_body_staticSources_routeTheoremBackedSeq
    P C Wh W IH hfrag hentry.toClosureBoundary

end Cpp
