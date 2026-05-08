import CppFormalization.Cpp2.Closure.Internal.SeqSelectedTailStaticAdequacySplitCI

namespace Cpp

/-!
# Closure.Internal.SeqSelectedTailStaticRouteTypingCI

A lower static-route layer for the selected tail of a sequence.

After `SeqSelectedTailStaticAdequacySplitCI`, the sequence payload is split into:

* left adequacy;
* selected-tail static;
* selected-tail adequacy for the selected static profile.

The selected-tail static component is not a runtime fact.  C++ reading: once the
normal post-environment of `s` has been selected in `s; t`, the tail `t` is
statically checked in that environment.  The actual state `σ1` and the concrete
head step are relevant to dynamic readiness and adequacy, but not to the static
shape of `t`.

This file therefore introduces a lower, state-independent static route-typing
support and lifts it back to the selected-route payload surface.
-/

/--
Lower selected-tail static route typing.

This is intentionally independent of:

* the actual post-state `σ1`;
* the concrete head-normal step proof;
* the normal-preservation core `P`.

It says: for a whole sequence boundary and a selected left-normal payload `hp`,
the tail is statically closed at the selected post-environment `hp.Θ`.
-/
structure SeqSelectedTailStaticRouteTypingCI : Type where
  static :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyStaticBoundaryCI hp.Θ t

/--
Lift lower static route typing to the current selected-tail static support.

The step and post-state arguments are deliberately ignored: the static boundary
for the tail depends on the selected post-environment, not on the runtime state.
-/
def SeqSelectedTailStaticRouteTypingCI.toSelectedTailStaticSupport
    (T : SeqSelectedTailStaticRouteTypingCI)
    (P : StmtNormalPreservationCoreCI) :
    SeqSelectedTailStaticSupportCI P :=
  { static := by
      intro Γ σ σ1 s t hentry _hstepHead hp
      exact T.static hentry hp }

/--
Adequacy support indexed by lower static route typing.

This keeps the important dependency: tail adequacy is for the profile chosen by
the lower static route-typing support.
-/
abbrev SeqSelectedTailAdequacyForStaticRouteTypingCI
    (T : SeqSelectedTailStaticRouteTypingCI)
    (P : StmtNormalPreservationCoreCI) : Type :=
  SeqSelectedTailAdequacyForStaticSupportCI
    (T.toSelectedTailStaticSupport P)

/--
Selected-route payload with the static route typing moved to a lower layer.

The closure-level semantic residuals are now:

* left adequacy for the head statement;
* tail adequacy for the static profile selected by `T`.

The tail static fact itself is supplied by `T`, which is a static/typing layer
object rather than a function-body-closure obligation.
-/
structure SeqSelectedHeadNormalRoutePayloadStaticRouteCI
    (P : StmtNormalPreservationCoreCI) : Type where
  tailStatic : SeqSelectedTailStaticRouteTypingCI
  leftAdequacy : SeqLeftAdequacyResidualCoreSupportCI P
  tailAdequacy :
    SeqSelectedTailAdequacyForStaticRouteTypingCI tailStatic P

namespace SeqSelectedHeadNormalRoutePayloadStaticRouteCI

/--
Forget the lower-static-route presentation to the previous split presentation.
-/
def toSplit
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadStaticRouteCI P) :
    SeqSelectedHeadNormalRoutePayloadSplitCI P :=
  { leftAdequacy := S.leftAdequacy
    tailStatic := S.tailStatic.toSelectedTailStaticSupport P
    tailAdequacy := S.tailAdequacy }

/-- Build the selected route through the previous split presentation. -/
def route
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadStaticRouteCI P)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstepHead : BigStepStmt σ s .normal σ1) :
    SeqHeadNormalRouteCI Γ σ s t σ1
      (seq_left_static_boundary_ci_of_entry hentry).profile :=
  S.toSplit.route hentry hstepHead

end SeqSelectedHeadNormalRoutePayloadStaticRouteCI

/--
Route selection support induced by the lower-static-route payload design.
-/
def seqTailRouteSelectionCoreSupportCI_of_staticRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadStaticRouteCI P) :
    SeqTailRouteSelectionCoreSupportCI P :=
  { select := by
      intro Γ σ σ1 s t hentry hstepHead
      exact S.route hentry hstepHead }

/--
Boundary-level sequence support from lower static route typing.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_staticRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadStaticRouteCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_selectedRoutePayloadSplit
    S.toSplit

/-
Design note: there is intentionally no constructor
`SeqSelectedHeadNormalRoutePayloadSplitCI → SeqSelectedHeadNormalRoutePayloadStaticRouteCI`.

The split payload can produce tail static data only after receiving an actual
head-normal step.  The lower route-typing object must produce tail static data
from the selected static route alone, without any runtime step.  Therefore the
reverse direction is not theorem-backed and should not be represented by a dummy
proof.
-/

end Cpp
