import CppFormalization.Cpp2.Closure.Internal.SeqSelectedRoutePayloadDesignCI

namespace Cpp

/-!
# Closure.Internal.SeqSelectedTailStaticAdequacySplitCI

Split the selected-tail route payload into its two honest responsibilities.

`SeqSelectedTailStaticAdequacySupportCI` was intentionally narrow, but it still
kept two different facts in one record:

* selected-tail static boundary at the post-environment chosen by the actual
  head-normal execution;
* adequacy of the selected tail profile at the actual post-state.

This file separates those two fields while keeping the dependency that matters:
the adequacy support is indexed by the selected static support, so it cannot talk
about an unrelated tail profile.

C++ reading: after `s` falls through in `s; t`, the type environment used for
`t` is the one selected by that concrete head-normal route.  The static fact
says that `t` is statically admissible there.  The adequacy fact says that the
chosen tail profile is semantically adequate at the actual post-state.
-/

/--
Selected-tail static support.

This is the static half of the selected-route tail payload.  It deliberately
still depends on the selected left-normal payload `hp`, because the tail is typed
at `hp.Θ`, not at an arbitrary caller-supplied environment.
-/
structure SeqSelectedTailStaticSupportCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  static :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (hp : SeqLeftNormalPayloadCI (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyStaticBoundaryCI hp.Θ t

/--
Selected-tail adequacy support for a fixed selected-tail static support.

The dependency on `S` is the point of the split: adequacy is always for the
profile selected by the corresponding static boundary.
-/
structure SeqSelectedTailAdequacyForStaticSupportCI
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedTailStaticSupportCI P) : Type where
  adequacy :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (hp : SeqLeftNormalPayloadCI (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyAdequacyCI hp.Θ σ1 t ((S.static hentry hstepHead hp).profile)

/-- Reassemble the previous combined selected-tail support from the split support. -/
def seqSelectedTailStaticAdequacySupportCI_of_split
    {P : StmtNormalPreservationCoreCI}
    (Sstatic : SeqSelectedTailStaticSupportCI P)
    (Sadequacy : SeqSelectedTailAdequacyForStaticSupportCI Sstatic) :
    SeqSelectedTailStaticAdequacySupportCI P :=
  { static := Sstatic.static
    adequacy := Sadequacy.adequacy }

namespace SeqSelectedTailStaticAdequacySupportCI

/-- Forget a combined selected-tail support to its static half. -/
def toStaticSupport
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedTailStaticAdequacySupportCI P) :
    SeqSelectedTailStaticSupportCI P :=
  { static := S.static }

/-- Forget a combined selected-tail support to its adequacy half indexed by its static projection. -/
def toAdequacyForStaticSupport
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedTailStaticAdequacySupportCI P) :
    SeqSelectedTailAdequacyForStaticSupportCI S.toStaticSupport :=
  { adequacy := S.adequacy }

end SeqSelectedTailStaticAdequacySupportCI

/--
Selected route payload with the selected-tail static and adequacy pieces split.

The remaining semantic/program-facing payloads are now explicit and correctly
ordered:

* left adequacy reflects the actual head-normal step into a selected left normal
  channel;
* tail static chooses the static profile for `t` at the selected post-environment;
* tail adequacy proves that that very profile is adequate at the actual
  post-state.
-/
structure SeqSelectedHeadNormalRoutePayloadSplitCI
    (P : StmtNormalPreservationCoreCI) : Type where
  leftAdequacy : SeqLeftAdequacyResidualCoreSupportCI P
  tailStatic : SeqSelectedTailStaticSupportCI P
  tailAdequacy : SeqSelectedTailAdequacyForStaticSupportCI tailStatic

namespace SeqSelectedHeadNormalRoutePayloadSplitCI

/-- Collapse the split payload to the previous combined selected-route payload design. -/
def toSelectedRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadSplitCI P) :
    SeqSelectedHeadNormalRoutePayloadCI P :=
  { leftAdequacy := S.leftAdequacy
    tail :=
      seqSelectedTailStaticAdequacySupportCI_of_split
        S.tailStatic S.tailAdequacy }

/-- Build the selected route from the split payload design. -/
def route
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadSplitCI P)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstepHead : BigStepStmt σ s .normal σ1) :
    SeqHeadNormalRouteCI Γ σ s t σ1
      (seq_left_static_boundary_ci_of_entry hentry).profile :=
  S.toSelectedRoutePayload.route hentry hstepHead

end SeqSelectedHeadNormalRoutePayloadSplitCI

/-- Route selection support induced by the split selected-route payload design. -/
def seqTailRouteSelectionCoreSupportCI_of_selectedRoutePayloadSplit
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadSplitCI P) :
    SeqTailRouteSelectionCoreSupportCI P :=
  { select := by
      intro Γ σ σ1 s t hentry hstepHead
      exact S.route hentry hstepHead }

/--
Boundary-level sequence support from the split selected-route payload design.

This is just the previous selected-route construction through the split-to-combined
adapter, but it exposes the residuals in the cleaner order for future work.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_selectedRoutePayloadSplit
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadSplitCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_selectedRoutePayload
    S.toSelectedRoutePayload

/--
Compatibility constructor from the previous combined selected-route payload to
the split interface.
-/
def seqSelectedHeadNormalRoutePayloadSplitCI_of_combined
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadCI P) :
    SeqSelectedHeadNormalRoutePayloadSplitCI P :=
  { leftAdequacy := S.leftAdequacy
    tailStatic := S.tail.toStaticSupport
    tailAdequacy := S.tail.toAdequacyForStaticSupport }

end Cpp
