import CppFormalization.Cpp2.Closure.Internal.SeqTailStabilityRouteCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureResultCI
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Boundary.Structural.SeqStructuralBoundaryProjectionCI

namespace Cpp

/-!
# Seq closure route assembly

Extracted from `FunctionBodyCaseSplitCI.lean`.
This file owns left/tail boundary reconstruction and the seq closure shell.
-/

/--
Normal-channel adequacy support for the extracted left boundary.

Unlike ordinary `BodyAdequacyCI.normalSound`, this does not merely return a bare
normal witness.  It returns the whole head-normal route needed to continue into
the tail.
-/
structure SeqLeftNormalAdequacyCI
    (Γ : TypeEnv) (σ : State) (s t : CppStmt)
    (P : BodyControlProfile Γ s) : Type where
  normalRoute :
    ∀ {σ1 : State} (_hstep : BigStepStmt σ s .normal σ1),
      SeqHeadNormalRouteCI Γ σ s t σ1 P

/--
Runtime decision for an actual left-return execution.

This is the return-side analogue of the route-aware normal branch.  Given an
actual execution

`BigStepStmt σ s (.returnResult rv) σ'`

the decision says that this execution is reflected by the selected return slot
of the extracted left profile.
-/
structure SeqLeftReturnRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (s : CppStmt)
    (P : BodyControlProfile Γ s)
    {rv : Option Value} {σ' : State}
    (_hstep : BigStepStmt σ s (.returnResult rv) σ') : Type where
  Delta : TypeEnv
  hleft : HasTypeStmtCI .returnK Γ s Delta
  hprofile : P.summary.returnOut = some ⟨Delta, hleft⟩

namespace SeqLeftReturnRuntimeDecisionCI

/-- Forget the runtime return decision to the older return-profile payload. -/
def toPayload
    {Γ : TypeEnv} {σ : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {rv : Option Value} {σ' : State}
    {hstep : BigStepStmt σ s (.returnResult rv) σ'}
    (d : SeqLeftReturnRuntimeDecisionCI Γ σ s P hstep) :
    SeqLeftReturnPayloadCI P :=
  { Delta := d.Delta
    hleft := d.hleft
    hprofile := d.hprofile }

/-- Forget the runtime return decision to ordinary adequacy evidence. -/
def toExists
    {Γ : TypeEnv} {σ : State} {s : CppStmt}
    {P : BodyControlProfile Γ s}
    {rv : Option Value} {σ' : State}
    {hstep : BigStepStmt σ s (.returnResult rv) σ'}
    (d : SeqLeftReturnRuntimeDecisionCI Γ σ s P hstep) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ s Δ},
      P.summary.returnOut = some out :=
  ⟨⟨d.Delta, d.hleft⟩, d.hprofile⟩

end SeqLeftReturnRuntimeDecisionCI

/--
Return-channel adequacy support for the extracted left boundary.

This is runtime-decision based: an actual left-return execution must match the
selected return slot in the extracted left profile.
-/
structure SeqLeftReturnAdequacyCI
    (Γ : TypeEnv) (σ : State) (s : CppStmt)
    (P : BodyControlProfile Γ s) : Type where
  returnDecision :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ s (.returnResult rv) σ'),
      SeqLeftReturnRuntimeDecisionCI Γ σ s P hstep

/--
Type-level package for the two semantic adequacy channels of the left side.

The normal channel is route-aware; the return channel is runtime-decision aware.
-/
structure SeqLeftAdequacySupportCI
    (Γ : TypeEnv) (σ : State) (s t : CppStmt)
    (P : BodyControlProfile Γ s) : Type where
  normal : SeqLeftNormalAdequacyCI Γ σ s t P
  returned : SeqLeftReturnAdequacyCI Γ σ s P

namespace SeqLeftAdequacySupportCI

/-- Forget the route-aware/runtime-decision support to ordinary `BodyAdequacyCI`. -/
def toBodyAdequacyCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (A : SeqLeftAdequacySupportCI Γ σ s t P) :
    BodyAdequacyCI Γ σ s P :=
  BodyAdequacyCI.ofWitness
    (normalWitness := by
      intro σ1 hstep
      let r := A.normal.normalRoute hstep
      exact ⟨⟨r.Θ, r.hleft⟩, r.hprofile⟩)
    (returnWitness := by
      intro rv σ' hstep
      let d := A.returned.returnDecision hstep
      exact ⟨⟨d.Delta, d.hleft⟩, d.hprofile⟩)

end SeqLeftAdequacySupportCI

/--
Remaining normal-profile payload obligation for an actual left-normal execution.

This is the left-side part of the head-normal route: the actual execution of
`s` must be reflected by the selected normal channel in the extracted left
profile.
-/
axiom seq_head_normal_profile_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    ∀ {σ1 : State},
      BigStepStmt σ s .normal σ1 →
      SeqLeftNormalPayloadCI hstatic.profile

/--
Remaining tail static+adequacy obligation for an actual left-normal execution.

This is the tail-side part of the head-normal route.  Once the actual head
execution has been reflected in the selected left normal payload, the tail
boundary must be supplied at that payload's post-environment and actual
post-state.
-/
axiom seq_tail_static_adequacy_payload_ci_of_head_normal_payload
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    ∀ {σ1 : State}
      (hstep : BigStepStmt σ s .normal σ1),
      SeqLeftNormalPayloadCI hstatic.profile →
      SeqTailStaticAdequacyPayloadCI
        (seq_head_normal_profile_payload_ci_of_entry hentry hstatic hstep).Θ
        σ1
        t

/--
Compatibility name for the full head-normal route.

The old route obligation is now assembled from two narrower obligations:
1. actual left-normal execution is reflected in the selected left normal profile;
2. the tail static/adequacy payload is supplied for that route.
-/
noncomputable def seq_head_normal_route_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    ∀ {σ1 : State},
      BigStepStmt σ s .normal σ1 →
      SeqHeadNormalRouteCI Γ σ s t σ1 hstatic.profile := by
  intro σ1 hstep
  let hp := seq_head_normal_profile_payload_ci_of_entry hentry hstatic hstep
  let htail :=
    seq_tail_static_adequacy_payload_ci_of_head_normal_payload
      hentry hstatic hstep hp
  exact
    { Θ := hp.Θ
      hleft := hp.hleft
      hprofile := hp.hprofile
      hstepLeft := hstep
      tail := htail }

/--
Compatibility wrapper: the left normal adequacy support is exactly the assembled
head-normal route provider.
-/
noncomputable def seq_left_normal_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    SeqLeftNormalAdequacyCI Γ σ s t hstatic.profile :=
  { normalRoute := seq_head_normal_route_ci_of_entry hentry hstatic }

/--
Operational embedding of a left-return execution into a whole-sequence return.

If the head of `s; t` returns, the tail is not evaluated.  This part is pure
operational semantics and should not be hidden inside the semantic adequacy
obligation.
-/
theorem seq_whole_return_step_of_left_return
    {σ σ' : State} {s t : CppStmt} {rv : Option Value}
    (hstep : BigStepStmt σ s (.returnResult rv) σ') :
    BigStepStmt σ (.seq s t) (.returnResult rv) σ' :=
  BigStepStmt.seqReturn (t := t) hstep

/--
Whole-sequence decision induced by an actual left-return execution.

This is the semantic bridge layer between the operational embedding
`seq_whole_return_step_of_left_return` and the selected left return slot.  The
indexed whole step records that the return route being read is exactly the
whole-sequence return produced from the head return.
-/
structure SeqLeftReturnWholeDecisionCI
    (Γ : TypeEnv) (σ : State) (s t : CppStmt)
    (P : BodyControlProfile Γ s)
    {rv : Option Value} {σ' : State}
    (hleftStep : BigStepStmt σ s (.returnResult rv) σ')
    (_hwholeStep : BigStepStmt σ (.seq s t) (.returnResult rv) σ') : Type where
  runtime : SeqLeftReturnRuntimeDecisionCI Γ σ s P hleftStep

/--
Remaining whole-return route decision obligation for the extracted left boundary.

The direct left-return runtime decision is no longer postulated here.  Instead,
we first embed the actual left return into the whole sequence, then read the
selected left return slot from that whole left-return route.
-/
axiom seq_left_return_whole_decision_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ s (.returnResult rv) σ'),
      SeqLeftReturnWholeDecisionCI Γ σ s t hstatic.profile hstep
        (seq_whole_return_step_of_left_return (t := t) hstep)

/--
Compatibility name for the old direct return-runtime decision provider.

This is now assembled from:
1. the theorem-backed operational embedding of a left return into `s; t`;
2. the whole-return route decision obligation.
-/
noncomputable def seq_left_return_runtime_decision_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ s (.returnResult rv) σ'),
      SeqLeftReturnRuntimeDecisionCI Γ σ s hstatic.profile hstep := by
  intro rv σ' hstep
  exact
    (seq_left_return_whole_decision_ci_of_entry
      hentry hstatic hstep).runtime

/--
Compatibility wrapper for the older return-adequacy name.

The old return adequacy package is now assembled from the runtime decision
provider.
-/
noncomputable def seq_left_return_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    SeqLeftReturnAdequacyCI Γ σ s hstatic.profile :=
  { returnDecision :=
      seq_left_return_runtime_decision_ci_of_entry hentry hstatic }

/--
Compatibility name for the old combined left adequacy support.

The combined package is now assembled from the two genuinely different
semantic obligations:
1. head-normal route support;
2. immediate left-return support.
-/
noncomputable def seq_left_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    SeqLeftAdequacySupportCI Γ σ s t hstatic.profile :=
  { normal := seq_left_normal_adequacy_ci_of_entry hentry hstatic
    returned := seq_left_return_adequacy_ci_of_entry hentry hstatic }

/-- Compatibility name for downstream callers. -/
noncomputable def seq_left_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    BodyAdequacyCI Γ σ s hstatic.profile :=
  (seq_left_adequacy_support_ci_of_entry hentry hstatic).toBodyAdequacyCI

/--
Compatibility scaffold for the left side of a sequence.

This name is kept for downstream callers, but the scaffold is no longer a
single opaque axiom.
-/
noncomputable def seq_left_closure_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    SeqLeftClosureScaffoldCI Γ σ s :=
  let hstatic := seq_left_static_boundary_ci_of_entry hentry
  { structural := seq_left_structural_boundary_of_structural hentry.structural
    static := hstatic
    adequacy := seq_left_adequacy_ci_of_entry hentry hstatic }

/--
Dynamic boundary for the left side of a sequence.

The left statement starts in the same state as the whole sequence.  Its dynamic
readiness is the left projection of the whole sequence readiness.
-/
def seq_left_dynamic_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyDynamicBoundary Γ σ s :=
  { state := hentry.dynamic.state
    safe := seq_ready_left hentry.dynamic.safe }

/--
Compatibility boundary for the left side of a sequence.

This assembles the already extracted left scaffold with the dynamic boundary
projected from the whole sequence boundary.
-/
noncomputable def seq_left_closure_boundary_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyClosureBoundaryCI Γ σ s := by
  let hs := seq_left_closure_scaffold_ci_of_entry hentry
  let hd := seq_left_dynamic_boundary_of_entry hentry
  exact mkBodyClosureBoundaryCI hs.structural hs.static hd hs.adequacy

/--
Selected head-normal execution exposes the route used to enter the sequence
tail.

This is the only honest way to obtain the tail static/adequacy package: the tail
environment is the selected route environment `route.Θ`, not an arbitrary
normal-witness environment supplied by a caller.
-/
noncomputable def seq_left_normalRoute_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstep : BigStepStmt σ s .normal σ1) :
    SeqHeadNormalRouteCI Γ σ s t σ1
      (seq_left_static_boundary_ci_of_entry hentry).profile :=
  (seq_left_adequacy_support_ci_of_entry
    hentry
    (seq_left_static_boundary_ci_of_entry hentry)).normal.normalRoute hstep

/--
Tail static+adequacy extracted from a selected head-normal route.

This replaces the old bare-witness obligation
`seq_tail_static_adequacy_payload_ci_of_left_normal`.  The result is indexed by
`route.Θ`, because that is the only environment justified by the selected
head-normal route.
-/
noncomputable def seq_tail_static_adequacy_ci_of_head_normal_route
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (_hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailStaticAdequacyCI route.Θ σ1 t :=
  route.tail.toStaticAdequacyCI

/--
Compatibility name for tail static+adequacy after an actual left-normal
execution.

The old version accepted an arbitrary `htyLeft`.  This version deliberately does
not: it first obtains the selected `SeqHeadNormalRouteCI` from the entry
boundary and the actual normal execution, then reads the tail package from that
route.
-/
noncomputable def seq_tail_static_adequacy_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {σ1 : State}
      (hstepLeft : BigStepStmt σ s .normal σ1),
      SeqTailStaticAdequacyCI
        (seq_left_normalRoute_of_entry hentry hstepLeft).Θ
        σ1
        t := by
  intro σ1 hstepLeft
  let route := seq_left_normalRoute_of_entry hentry hstepLeft
  exact seq_tail_static_adequacy_ci_of_head_normal_route hentry route

/--
Compatibility projection: tail static boundary after a selected left-normal
route.
-/
noncomputable def seq_tail_static_boundary_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {σ1 : State}
      (hstepLeft : BigStepStmt σ s .normal σ1),
      BodyStaticBoundaryCI
        (seq_left_normalRoute_of_entry hentry hstepLeft).Θ
        t := by
  intro σ1 hstepLeft
  exact (seq_tail_static_adequacy_ci_of_left_normal hentry hstepLeft).static

/--
Compatibility projection: tail adequacy after a selected left-normal route.
-/
noncomputable def seq_tail_adequacy_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {σ1 : State}
      (hstepLeft : BigStepStmt σ s .normal σ1),
      BodyAdequacyCI
        (seq_left_normalRoute_of_entry hentry hstepLeft).Θ
        σ1
        t
        ((seq_tail_static_boundary_ci_of_left_normal hentry hstepLeft).profile) := by
  intro σ1 hstepLeft
  exact (seq_tail_static_adequacy_ci_of_left_normal hentry hstepLeft).adequacy

/--
Compatibility scaffold for the sequence tail after a selected left-normal route.

The result is indexed by the route-selected environment.  This is intentional:
there is no honest way to return a tail scaffold for an arbitrary `Θ` supplied
by a bare normal typing witness.
-/
noncomputable def seq_tail_closure_scaffold_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {σ1 : State}
      (hstepLeft : BigStepStmt σ s .normal σ1),
      SeqTailClosureScaffoldCI
        (seq_left_normalRoute_of_entry hentry hstepLeft).Θ
        σ1
        t := by
  intro σ1 hstepLeft
  let htail := seq_tail_static_adequacy_ci_of_left_normal hentry hstepLeft
  exact
    { structural := seq_tail_structural_boundary_of_structural hentry.structural
      static := htail.static
      adequacy := htail.adequacy }
/--
Tail scaffold extracted from a selected head-normal route.

This is the preferred route-aware form: the tail static/adequacy package comes
from the route itself, not from an arbitrary normal witness.
-/
noncomputable def seq_tail_closure_scaffold_ci_of_head_normal_route
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    SeqTailClosureScaffoldCI route.Θ σ1 t :=
  { structural := seq_tail_structural_boundary_of_structural hentry.structural
    static := route.tail.static
    adequacy := route.tail.support.toBodyAdequacyCI }

/--
Tail closure boundary extracted from a selected head-normal route.

Compatibility surface: internally this now factors through the route-local
`SeqTailStabilityAtRouteCI` obligation and then forgets the resulting full
continuation boundary back to `BodyClosureBoundaryCI`.
-/
noncomputable def seq_tail_closure_boundary_ci_of_head_normal_route
    (_mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    BodyClosureBoundaryCI route.Θ σ1 t := by
  let stability := seq_tail_stability_at_route_ci_of_entry hentry route
  exact
    seq_tail_closure_boundary_ci_of_head_normal_route_from_stability
      hentry route stability


/--
Compatibility name for tail closure after an actual left-normal execution.

This no longer accepts an arbitrary normal typing witness. It obtains the
selected head-normal route from the entry boundary and the actual left-normal
execution, then delegates to the route-aware boundary constructor.
-/
noncomputable def seq_tail_closure_boundary_ci_of_left_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {σ1 : State}
      (hstepLeft : BigStepStmt σ s .normal σ1),
      BodyClosureBoundaryCI
        (seq_left_normalRoute_of_entry hentry hstepLeft).Θ
        σ1
        t := by
  intro σ1 hstepLeft
  exact
    seq_tail_closure_boundary_ci_of_head_normal_route
      mkWhileReentry
      hentry
      (seq_left_normalRoute_of_entry hentry hstepLeft)

/--
Actual head-normal execution exposes a normal CI witness for the left statement.

This is the theorem version of the previously explicit `normalWitness`
callback. It is not guessed from the whole sequence profile. It is obtained from
the left closure boundary's adequacy, which is exactly the layer that relates
actual execution to the static control profile.
-/
theorem seq_left_normalWitness_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstep : BigStepStmt σ s .normal σ1) :
    ∃ Δ, HasTypeStmtCI .normalK Γ s Δ := by
  let route := seq_left_normalRoute_of_entry hentry hstep
  exact ⟨route.Θ, route.hleft⟩


/--
Route-aware seq shell with an explicit route-local tail stability callback.

This is the clean decomposition surface:

* `SeqHeadNormalRouteCI` says which left-normal route actually occurred;
* `SeqTailStabilityAtRouteCI` says the route did not break the tail dynamic
  entry conditions;
* `StmtContinuationBoundaryCI` is assembled from route static/adequacy plus
  that stability proof.
-/
theorem seq_function_body_closure_boundary_ci_honest_continuation_with_stability
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailStability :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailStabilityAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  have hleft : FunctionBodyClosureResult σ s :=
    leftClosure (seq_left_closure_boundary_ci_of_entry hentry)
  exact
    seq_function_body_result_return_aware
      hleft
      (fun hstep =>
        let route := seq_left_normalRoute_of_entry hentry hstep
        let htailBoundary :=
          seq_tail_continuation_boundary_ci_of_head_normal_route
            hentry route (tailStability route)
        tailClosure route htailBoundary)

/--
Body-boundary version of the explicit-stability seq shell.

The callback still receives the selected route, but the post-state continuation
is forgotten to the old `BodyClosureBoundaryCI` surface for compatibility.
-/
theorem seq_function_body_closure_boundary_ci_honest_with_stability
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailStability :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        SeqTailStabilityAtRouteCI route)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyClosureBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_continuation_with_stability
      hentry
      leftClosure
      tailStability
      (fun route htail =>
        tailClosure route htail.toBodyClosureBoundaryCI)

/--
Route-aware theorem version of the seq shell.

Compatibility surface.  The implementation now enters the tail through the
route-local stability contract; the old `mkWhileReentry` argument is retained
for downstream callers but is no longer the conceptual source of tail dynamic
readiness.
-/
theorem seq_function_body_closure_boundary_ci_honest
    (_mkWhileReentry : WhileReentryReadyProvider)
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
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest_with_stability
      hentry
      leftClosure
      (fun route => seq_tail_stability_at_route_ci_of_entry hentry route)
      tailClosure

/--
Route-aware `BodyReadyCI` wrapper for sequence closure.

This is the canonical ready-level surface.  The tail callback receives the
selected head-normal route and the tail boundary at `route.Θ`; it no longer
chooses an arbitrary post-environment from a bare normal typing witness.
-/
theorem seq_function_body_closure_ci_honest
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry.toClosureBoundary).profile) →
        BodyReadyCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest
      mkWhileReentry
      hentry.toClosureBoundary
      (fun hleftBoundary => leftClosure hleftBoundary.toBodyReadyCI)
      (fun route htailBoundary =>
        tailClosure route htailBoundary.toBodyReadyCI)



end Cpp
