import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyStructuralBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyControlProfile
import CppFormalization.Cpp2.Closure.Foundation.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

abbrev FunctionBodyClosureResult (σ : State) (st : CppStmt) : Prop :=
  (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

/-!
## Seq scaffold extraction

The old `seq_left_closure_scaffold_ci_of_entry` and
`seq_tail_closure_scaffold_ci_of_left_normal` axioms hid several different
responsibilities in one package. This file keeps the public scaffold names for
downstream compatibility, but builds them from narrower pieces:

* structural data is theorem-backed from the whole sequence boundary;
* left `typed0` is theorem-backed from the whole old typing payload;
* whole-sequence normal/return profile payloads are decomposed into explicit
  `Prop`-level seq provenance certificates;
* left static profile/root/coherence is now supplied together with an explicit
  compatibility certificate against the seq provenance;
* left adequacy remains a separate semantic obligation;
* tail static and tail adequacy are packaged together behind the actual
  left-normal route, because the tail environment is path-sensitive and must not
  be projected from the whole sequence return channel.
-/

structure SeqLeftClosureScaffoldCI
    (Γ : TypeEnv) (σ : State) (s : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ s
  static : BodyStaticBoundaryCI Γ s
  adequacy : BodyAdequacyCI Γ σ s static.profile

structure SeqTailClosureScaffoldCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  structural : BodyStructuralBoundary Θ t
  static : BodyStaticBoundaryCI Θ t
  adequacy : BodyAdequacyCI Θ σ1 t static.profile

/--
Static scaffold for the left side of a sequence, excluding the old `typed0`
payload.

`typed0` is theorem-backed from the whole sequence's coarse typing below.
The remaining static data is the chosen CI profile/root/coherence for `s`.
-/
structure SeqLeftStaticScaffoldCI
    (Γ : TypeEnv) (s : CppStmt) : Type where
  profile : BodyControlProfile Γ s
  root : BodyEntryWitness Γ s
  rootCoherent : BodyRootCoherent profile root

namespace SeqLeftStaticScaffoldCI

/-- Assemble the canonical left static boundary from theorem-backed `typed0`. -/
def toBodyStaticBoundaryCI
    {Γ : TypeEnv} {s : CppStmt}
    (h : SeqLeftStaticScaffoldCI Γ s)
    (htyped : WellTypedFrom Γ s) :
    BodyStaticBoundaryCI Γ s :=
  { typed0 := htyped
    profile := h.profile
    root := h.root
    rootCoherent := h.rootCoherent }

end SeqLeftStaticScaffoldCI

/--
Static and adequacy payload for the tail of a sequence after an actual
left-normal route.

This package is deliberately produced from the actual normal typing and
execution route below. Keeping static and adequacy together prevents the tail
adequacy obligation from degenerating into an over-broad statement about
arbitrary post-states and arbitrary static packages.
-/
structure SeqTailStaticAdequacyCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  static : BodyStaticBoundaryCI Θ t
  adequacy : BodyAdequacyCI Θ σ1 t static.profile

/--
Normal channel provenance for a whole sequence payload.

This must live in `Prop`, not `Type`, because it is obtained by eliminating
a `HasTypeStmtCI` proof, and `HasTypeStmtCI` itself is a `Prop`.
-/
inductive SeqNormalSourceCI
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}) : Prop where
  | normal
      {Θ Δ : TypeEnv}
      (hleft : HasTypeStmtCI .normalK Γ s Θ)
      (htail : HasTypeStmtCI .normalK Θ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩) :
      SeqNormalSourceCI out

/--
Return channel provenance for a whole sequence payload.

A sequence can return either because the left side returns, or because
the left side is normal and the tail returns.
-/
inductive SeqReturnSourceCI
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}) : Prop where
  | leftReturn
      {Δ : TypeEnv}
      (hleft : HasTypeStmtCI .returnK Γ s Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.seq_return hleft⟩) :
      SeqReturnSourceCI out
  | tailReturn
      {Θ Δ : TypeEnv}
      (hleft : HasTypeStmtCI .normalK Γ s Θ)
      (htail : HasTypeStmtCI .returnK Θ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩) :
      SeqReturnSourceCI out

theorem seq_normal_source_ci_of_out
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}) :
    SeqNormalSourceCI out := by
  rcases out with ⟨Δ, hty⟩
  cases hty with
  | seq_normal hleft htail =>
      exact SeqNormalSourceCI.normal hleft htail rfl

theorem seq_return_source_ci_of_out
    {Γ : TypeEnv} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}) :
    SeqReturnSourceCI out := by
  rcases out with ⟨Δ, hty⟩
  cases hty with
  | seq_normal hleft htail =>
      exact SeqReturnSourceCI.tailReturn hleft htail rfl
  | seq_return hleft =>
      exact SeqReturnSourceCI.leftReturn hleft rfl

/-- Extract the left normal payload from a whole-sequence normal source. -/
theorem seq_normal_source_left_payload_ci
    {Γ : TypeEnv} {s t : CppStmt}
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}}
    (hsrc : SeqNormalSourceCI out) :
    ∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
      ∃ Δ, ∃ htail : HasTypeStmtCI .normalK Θ t Δ,
        out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩ := by
  cases hsrc with
  | normal hleft htail hout =>
      exact ⟨_, hleft, _, htail, hout⟩

/--
Extract the left-side payload required by a whole-sequence return source.

A left-return source gives a left return payload.  A tail-return source gives a
left normal payload, because the tail is reached only after the left side falls
through normally.
-/
theorem seq_return_source_left_payload_ci
    {Γ : TypeEnv} {s t : CppStmt}
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}}
    (hsrc : SeqReturnSourceCI out) :
    (∃ Δ, ∃ hleft : HasTypeStmtCI .returnK Γ s Δ,
        out = ⟨Δ, HasTypeStmtCI.seq_return hleft⟩) ∨
      (∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
        ∃ Δ, ∃ htail : HasTypeStmtCI .returnK Θ t Δ,
          out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩) := by
  cases hsrc with
  | leftReturn hleft hout =>
      exact Or.inl ⟨_, hleft, hout⟩
  | tailReturn hleft htail hout =>
      exact Or.inr ⟨_, hleft, _, htail, hout⟩

/--
Provenance certificate for the static channels of a whole sequence boundary.

This is a proposition, not data.  It records that every visible whole-sequence
channel has the expected seq provenance.
-/
structure SeqStaticDecompositionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) : Prop where
  normal :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      SeqNormalSourceCI out
  returned :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
      SeqReturnSourceCI out

theorem seq_static_decomposition_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    SeqStaticDecompositionCI hentry := by
  refine
    { normal := ?_
      returned := ?_ }
  · intro out _hout
    exact seq_normal_source_ci_of_out out
  · intro out _hout
    exact seq_return_source_ci_of_out out

/--
Compatibility condition for a chosen left static scaffold.

This is still a proposition, but unlike the earlier opaque scaffold axiom it
states what the left profile must expose:
- any visible whole-sequence normal channel contributes a left normal channel;
- a visible whole-sequence return channel contributes either a left return
  channel or a left normal channel, depending on whether the return originates
  in the head or in the tail.

The condition deliberately does not force the left profile to be minimal.  It
only requires the channels demanded by the visible whole-sequence profile.
-/
structure SeqLeftStaticScaffoldCompatibleCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (_D : SeqStaticDecompositionCI hentry)
    (S : SeqLeftStaticScaffoldCI Γ s) : Prop where
  normalFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      ∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
        S.profile.summary.normalOut = some ⟨Θ, hleft⟩
  returnFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
        (∃ Δ, ∃ hleft : HasTypeStmtCI .returnK Γ s Δ,
          S.profile.summary.returnOut = some ⟨Δ, hleft⟩) ∨
        (∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
          S.profile.summary.normalOut = some ⟨Θ, hleft⟩)

/--
The left side of a well-typed sequence is well typed.

This is deliberately proved from the coarse `typed0` payload of the whole
sequence. It is not guessed from a CI root witness, because a return/break root
by itself does not generally carry enough information to type unrelated sequence
tails.
-/
theorem seq_left_typed0_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    WellTypedFrom Γ s := by
  rcases hentry.static.typed0 with ⟨Δ, htySeq⟩
  cases htySeq with
  | seq hs _ht =>
      exact ⟨_, hs⟩

/-- The left side inherits structural admissibility from the whole sequence. -/
theorem seq_left_structural_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStructuralBoundary Γ s := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/-- The tail side inherits structural admissibility from the whole sequence. -/
theorem seq_tail_structural_boundary_of_entry
    {Γ Θ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStructuralBoundary Θ t := by
  have hwf : WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.2
      breakScoped := hbreak.2
      continueScoped := hcont.2 }

/--
Remaining static-profile/root obligation for extracting the left side of a
sequence.

The result is a chosen left static scaffold together with a compatibility
certificate against the theorem-backed seq decomposition.  This is narrower than
an arbitrary projection from the whole sequence: the chosen left profile must
expose exactly the head-side channels required by the visible whole-sequence
normal/return channels.
-/
axiom seq_left_static_scaffold_payload_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) :
    { S : SeqLeftStaticScaffoldCI Γ s //
      SeqLeftStaticScaffoldCompatibleCI hentry D S }

/-- Compatibility projection for the chosen left static scaffold. -/
noncomputable def seq_left_static_scaffold_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) :
    SeqLeftStaticScaffoldCI Γ s :=
  (seq_left_static_scaffold_payload_ci_of_decomposition hentry D).1

/-- The compatibility certificate carried by the chosen left static scaffold. -/
theorem seq_left_static_scaffold_compatible_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) :
    SeqLeftStaticScaffoldCompatibleCI hentry D
      (seq_left_static_scaffold_ci_of_decomposition hentry D) :=
  (seq_left_static_scaffold_payload_ci_of_decomposition hentry D).2

/-- Compatibility name for downstream callers. -/
noncomputable def seq_left_static_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    SeqLeftStaticScaffoldCI Γ s :=
  seq_left_static_scaffold_ci_of_decomposition
    hentry
    (seq_static_decomposition_ci_of_entry hentry)

/-- Compatibility certificate for the downstream-name scaffold. -/
theorem seq_left_static_scaffold_compatible_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    SeqLeftStaticScaffoldCompatibleCI hentry
      (seq_static_decomposition_ci_of_entry hentry)
      (seq_left_static_scaffold_ci_of_entry hentry) :=
  seq_left_static_scaffold_compatible_ci_of_decomposition
    hentry
    (seq_static_decomposition_ci_of_entry hentry)

/--
Remaining semantic adequacy obligation for the extracted left boundary.

Kept separate from static extraction: adequacy relates actual executions to the
chosen static profile, so it should not be hidden inside a static scaffold.
-/
axiom seq_left_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    BodyAdequacyCI Γ σ s hstatic.profile

/-- Left static boundary assembled from theorem-backed `typed0` and the static scaffold. -/
noncomputable def seq_left_static_boundary_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStaticBoundaryCI Γ s :=
  (seq_left_static_scaffold_ci_of_entry hentry).toBodyStaticBoundaryCI
    (seq_left_typed0_of_entry hentry)

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
  { structural := seq_left_structural_boundary_of_entry hentry
    static := hstatic
    adequacy := seq_left_adequacy_ci_of_entry hentry hstatic }

/--
Remaining tail static+adequacy obligation after an actual left-normal route.

The premise is intentionally route-indexed. The selected
`HasTypeStmtCI .normalK Γ s Θ` and the actual `BigStepStmt σ s .normal σ1`
determine the tail environment and post-state. A tail adequacy provider that
does not mention this route is too strong and mathematically misleading.
-/
axiom seq_tail_static_adequacy_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      SeqTailStaticAdequacyCI Θ σ1 t

/--
Compatibility projection: tail static boundary after a left-normal route.
Prefer the packaged `seq_tail_static_adequacy_ci_of_left_normal` in new code.
-/
noncomputable def seq_tail_static_boundary_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      BodyStaticBoundaryCI Θ t := by
  intro Θ σ1 htyLeft hstepLeft
  exact (seq_tail_static_adequacy_ci_of_left_normal hentry htyLeft hstepLeft).static

/--
Compatibility projection: tail adequacy after a left-normal route.
Prefer the packaged `seq_tail_static_adequacy_ci_of_left_normal` in new code.
-/
noncomputable def seq_tail_adequacy_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State}
      (htyLeft : HasTypeStmtCI .normalK Γ s Θ)
      (hstepLeft : BigStepStmt σ s .normal σ1),
      BodyAdequacyCI Θ σ1 t
        ((seq_tail_static_boundary_ci_of_left_normal hentry htyLeft hstepLeft).profile) := by
  intro Θ σ1 htyLeft hstepLeft
  exact (seq_tail_static_adequacy_ci_of_left_normal hentry htyLeft hstepLeft).adequacy

/--
Compatibility scaffold for the sequence tail after a left-normal execution.

This is now assembled from theorem-backed structural extraction plus the
route-indexed tail static+adequacy package.
-/
noncomputable def seq_tail_closure_scaffold_ci_of_left_normal
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      SeqTailClosureScaffoldCI Θ σ1 t := by
  intro Θ σ1 htyLeft hstepLeft
  let htail := seq_tail_static_adequacy_ci_of_left_normal hentry htyLeft hstepLeft
  exact
    { structural := seq_tail_structural_boundary_of_entry hentry
      static := htail.static
      adequacy := htail.adequacy }

def seq_left_dynamic_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyDynamicBoundary Γ σ s :=
  { state := hentry.dynamic.state
    safe := seq_ready_left hentry.dynamic.safe }

noncomputable def seq_left_closure_boundary_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyClosureBoundaryCI Γ σ s := by
  let hs := seq_left_closure_scaffold_ci_of_entry hentry
  let hd := seq_left_dynamic_boundary_of_entry hentry
  exact mkBodyClosureBoundaryCI hs.structural hs.static hd hs.adequacy

noncomputable def seq_tail_closure_boundary_ci_of_left_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    ∀ {Θ : TypeEnv} {σ1 : State},
      HasTypeStmtCI .normalK Γ s Θ →
      BigStepStmt σ s .normal σ1 →
      BodyClosureBoundaryCI Θ σ1 t := by
  intro Θ σ1 htyLeft hstepLeft
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      mkWhileReentry htyLeft hentry.dynamic.state hreadyLeft hstepLeft
  have hreadyRight : StmtReadyConcrete Θ σ1 t :=
    seq_ready_right_after_left_normal htyLeft hσ1 hentry.dynamic.safe hstepLeft
  let hs := seq_tail_closure_scaffold_ci_of_left_normal hentry htyLeft hstepLeft
  let hd : BodyDynamicBoundary Θ σ1 t :=
    { state := hσ1
      safe := hreadyRight }
  exact mkBodyClosureBoundaryCI hs.structural hs.static hd hs.adequacy

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
  let hleft : BodyClosureBoundaryCI Γ σ s :=
    seq_left_closure_boundary_ci_of_entry hentry
  rcases hleft.adequacy.normalSound hstep with ⟨out, _hout⟩
  exact ⟨out.1, out.2⟩

/--
Return-aware theorem version of the old seq shell.

The old axiom hid the central issue: tail closure may only be invoked after an
actual head-normal execution, and it needs the corresponding normal CI witness.
That witness is now supplied by `seq_left_normalWitness_of_entry`, which follows
from left-boundary adequacy.
-/
theorem seq_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyClosureBoundaryCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  have hleft : FunctionBodyClosureResult σ s :=
    leftClosure (seq_left_closure_boundary_ci_of_entry hentry)
  exact
    seq_function_body_result_return_aware
      hleft
      (fun hstep =>
        match seq_left_normalWitness_of_entry hentry hstep with
        | ⟨Δ, htyLeft⟩ =>
            tailClosure htyLeft hstep (tailBoundary htyLeft hstep))

axiom ite_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t))
    (thenClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyClosureBoundaryCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t)

theorem seq_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.seq s t))
    (leftClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (tailBoundary :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t)
    (tailClosure :
      ∀ {Δ : TypeEnv} {σ1 : State},
        HasTypeStmtCI .normalK Γ s Δ →
        BigStepStmt σ s .normal σ1 →
        BodyReadyCI Δ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) := by
  exact
    seq_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hleftBoundary => leftClosure hleftBoundary.toBodyReadyCI)
      (fun hty hstep => (tailBoundary hty hstep).toClosureBoundary)
      (fun hty hstep htailBoundary =>
        tailClosure hty hstep htailBoundary.toBodyReadyCI)

theorem ite_function_body_closure_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyReadyCI Γ σ (.ite c s t))
    (thenClosure :
      BodyReadyCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyReadyCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  exact
    ite_function_body_closure_boundary_ci_honest
      hentry.toClosureBoundary
      (fun hthenBoundary => thenClosure hthenBoundary.toBodyReadyCI)
      (fun helseBoundary => elseClosure helseBoundary.toBodyReadyCI)

end Cpp
