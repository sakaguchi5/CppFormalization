import CppFormalization.Cpp2.Route.ContinuationRoute.Seq
import CppFormalization.Cpp2.Route.Closure.SeqBoundaryStaticDecompositionCI
import CppFormalization.Cpp2.Preservation.Closure.SequentialNormalPreservation
import CppFormalization.Cpp2.Route.Closure.SeqScaffoldRouteCI

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

end Cpp
