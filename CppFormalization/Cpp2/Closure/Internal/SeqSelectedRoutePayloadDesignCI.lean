import CppFormalization.Cpp2.Closure.Internal.SeqRouteTheoremBackedCoreSupportCI

namespace Cpp

/-!
# Closure.Internal.SeqSelectedRoutePayloadDesignCI

A cleaner design for the remaining selected-route payload of sequence closure.

After the route-aware refactoring, the remaining responsibility is not tail
boundary reconstruction.  The selected route itself must be justified:

* the actual head-normal execution of `s` is reflected by the selected left
  normal channel;
* the tail `t` has a static boundary at that selected post-environment;
* that tail static profile is adequate at the actual post-state.

This file makes that design explicit.  The first item is not a new axiom: it is
exactly the normal channel of the left adequacy residual.  The second and third
items are kept as a route-indexed tail static/adequacy support, because they are
about entering `t` at the selected post-environment/state.
-/

/--
Convert ordinary body adequacy into the channel-split tail adequacy support used
by the route payload layer.
-/
def seqTailAdequacySupportCI_of_bodyAdequacyCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    {P : BodyControlProfile Θ t}
    (A : BodyAdequacyCI Θ σ1 t P) :
    SeqTailAdequacySupportCI Θ σ1 t P :=
  { normal :=
      { normalSound := by
          intro σ2 hstep
          let w := A.normalWitness hstep
          exact ⟨w.val, w.property⟩ }
    returned :=
      { returnSound := by
          intro rv σ2 hstep
          let w := A.returnWitness hstep
          exact ⟨w.val, w.property⟩ } }

/--
The selected left normal payload is theorem-backed by the left adequacy field.

C++ reading: if the head statement `s` actually falls through normally, then the
left profile used to analyse `s; t` must expose that normal exit.  This is not a
whole-sequence normal fact: the tail may diverge, return, or continue with a
state-dependent behavior.  It is exactly the local normal adequacy of `s`.
-/
def seq_left_normal_payload_ci_of_left_adequacy
    {Γ : TypeEnv} {σ σ1 : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    (A : BodyAdequacyCI Γ σ s P)
    (hstep : BigStepStmt σ s .normal σ1) :
    SeqLeftNormalPayloadCI P :=
  let w := A.normalWitness hstep
  { Θ := w.val.val
    hleft := w.val.property
    hprofile := w.property }

/--
Route-indexed tail static/adequacy support for a selected left-normal payload.

This is the honest residual after extracting the left-normal payload from left
adequacy.  It says: once `s` has actually fallen through and the selected left
normal payload has chosen the post-environment `hp.Θ`, the tail `t` has a static
boundary at `hp.Θ`, and that static profile is adequate at the actual post-state.

The static and adequacy fields are deliberately kept together.  The adequacy is
for the profile chosen by the static boundary, so splitting them into unrelated
arguments would recreate the old over-broad tail obligation.
-/
structure SeqSelectedTailStaticAdequacySupportCI
    (_P : StmtNormalPreservationCoreCI) : Type where
  static :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (hp : SeqLeftNormalPayloadCI (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyStaticBoundaryCI hp.Θ t

  adequacy :
    ∀ {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (hstepHead : BigStepStmt σ s .normal σ1) →
      (hp : SeqLeftNormalPayloadCI (seq_left_static_boundary_ci_of_entry hentry).profile) →
      BodyAdequacyCI hp.Θ σ1 t ((static hentry hstepHead hp).profile)

namespace SeqSelectedTailStaticAdequacySupportCI

/-- Convert the selected-tail support into the route payload expected by `SeqHeadNormalRouteCI`. -/
def toRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedTailStaticAdequacySupportCI P)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstepHead : BigStepStmt σ s .normal σ1)
    (hp : SeqLeftNormalPayloadCI (seq_left_static_boundary_ci_of_entry hentry).profile) :
    SeqTailStaticAdequacyPayloadCI hp.Θ σ1 t :=
  { static := S.static hentry hstepHead hp
    support :=
      seqTailAdequacySupportCI_of_bodyAdequacyCI
        (S.adequacy hentry hstepHead hp) }

end SeqSelectedTailStaticAdequacySupportCI

/--
Selected head-normal route payload support.

This is the intended replacement design for the two older head-normal route
payload obligations:

* left-normal reflection is obtained from the left adequacy residual;
* selected-tail static/adequacy is the remaining route-indexed tail payload.
-/
structure SeqSelectedHeadNormalRoutePayloadCI
    (P : StmtNormalPreservationCoreCI) : Type where
  leftAdequacy : SeqLeftAdequacyResidualCoreSupportCI P
  tail : SeqSelectedTailStaticAdequacySupportCI P

namespace SeqSelectedHeadNormalRoutePayloadCI

/--
Build the selected head-normal route from the new payload design.

No whole-sequence normal result is required.  The head-normal step itself is
reflected by the left adequacy residual, and the selected tail payload supplies
entry data for `t` at the resulting environment/state.
-/
def route
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadCI P)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstepHead : BigStepStmt σ s .normal σ1) :
    SeqHeadNormalRouteCI Γ σ s t σ1
      (seq_left_static_boundary_ci_of_entry hentry).profile :=
  let hp :=
    seq_left_normal_payload_ci_of_left_adequacy
      (S.leftAdequacy.leftAdequacy hentry)
      hstepHead
  { Θ := hp.Θ
    hleft := hp.hleft
    hprofile := hp.hprofile
    hstepLeft := hstepHead
    tail := S.tail.toRoutePayload hentry hstepHead hp }

end SeqSelectedHeadNormalRoutePayloadCI

/-- Route selection support induced by the selected-route payload design. -/
def seqTailRouteSelectionCoreSupportCI_of_selectedRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadCI P) :
    SeqTailRouteSelectionCoreSupportCI P :=
  { select := by
      intro Γ σ σ1 s t hentry hstepHead
      exact S.route hentry hstepHead }

/--
Boundary-level sequence support from the selected-route payload design.

At this level, all non-adequacy reconstruction is projection/theorem-backed:
left structural/static/dynamic come from the sequence entry, route dynamic comes
from the pure preservation core, and tail static is projected from the selected
route payload.  The semantic adequacy residuals are exactly the two fields inside
`SeqSelectedHeadNormalRoutePayloadCI`:

* left adequacy of `s`;
* selected-tail adequacy of `t` after an actual head-normal step.
-/
noncomputable def seqFunctionBodyClosureBoundaryCoreSupportCI_of_selectedRoutePayload
    {P : StmtNormalPreservationCoreCI}
    (S : SeqSelectedHeadNormalRoutePayloadCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_routedComponents
    (seq_left_boundary_of_adequacy_residual S.leftAdequacy)
    (seqTailRouteSelectionCoreSupportCI_of_selectedRoutePayload S)
    (seqTailBoundaryComponentsAtRouteCoreSupportCI_of_routeTheoremBacked
      (seqTailAdequacyForSelectedRouteCoreSupportCI_of_routePayload P))

end Cpp
