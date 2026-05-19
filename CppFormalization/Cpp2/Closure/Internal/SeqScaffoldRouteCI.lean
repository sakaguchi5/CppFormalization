import CppFormalization.Cpp2.Boundary.FunctionBody
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.Pure.BodyStructuralBoundary
import CppFormalization.Cpp2.Typing.ControlProfile
import CppFormalization.Cpp2.Static.Safety.BodyDynamicBoundary
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Internal.SequentialNormalPreservation
import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Static.Safety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Semantics.Divergence
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureResultCI

namespace Cpp

/-!
# Seq scaffold and selected-route core

Extracted from `FunctionBodyCaseSplitCI.lean`.
This file owns the seq scaffold/static/slot/selected-route layer.
-/

/-!
## Seq scaffold extraction

The old `seq_left_closure_scaffold_ci_of_entry` and
`seq_tail_closure_scaffold_ci_of_left_normal` axioms hid several different
responsibilities in one package. The canonical sequence closure surfaces in
this file are now route-aware: the tail is entered through the selected
`SeqHeadNormalRouteCI`, not through an arbitrary bare normal typing witness.
The old explicit-tail-boundary surfaces have been removed from this file; callers should use the selected-route callback shape.

The scaffold pieces are built from narrower pieces:

* structural data is theorem-backed from the whole sequence boundary;
* left `typed0` is theorem-backed from the whole old typing payload;
* whole-sequence normal/return profile payloads are decomposed into explicit
  `Prop`-level seq provenance certificates;
* left profile selection and left root/coherence selection are separated;
* root/coherence is definitionally assembled from Type-level profile support;
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
Compatibility condition for a chosen left profile.

This is a proposition. It is useful for downstream reasoning, but it must not
be used to construct Type-level root data.
-/
structure SeqLeftProfileCompatibleCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (_D : SeqStaticDecompositionCI hentry)
    (P : BodyControlProfile Γ s) : Prop where
  normalFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      ∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
        P.summary.normalOut = some ⟨Θ, hleft⟩
  returnFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
        (∃ Δ, ∃ hleft : HasTypeStmtCI .returnK Γ s Δ,
          P.summary.returnOut = some ⟨Δ, hleft⟩) ∨
        (∃ Θ, ∃ hleft : HasTypeStmtCI .normalK Γ s Θ,
          P.summary.normalOut = some ⟨Θ, hleft⟩)

/--
Type-level payload witnessing that the chosen left profile exposes a normal
channel.

The equality proof is a Prop field inside a Type-valued structure.  This avoids
trying to use `Sigma` with a Prop-valued family.
-/
structure SeqLeftNormalPayloadCI
    {Γ : TypeEnv} {s : CppStmt}
    (P : BodyControlProfile Γ s) : Type where
  Θ : TypeEnv
  hleft : HasTypeStmtCI .normalK Γ s Θ
  hprofile : P.summary.normalOut = some ⟨Θ, hleft⟩

/--
Type-level payload witnessing that the chosen left profile exposes a return
channel.
-/
structure SeqLeftReturnPayloadCI
    {Γ : TypeEnv} {s : CppStmt}
    (P : BodyControlProfile Γ s) : Type where
  Delta : TypeEnv
  hleft : HasTypeStmtCI .returnK Γ s Delta
  hprofile : P.summary.returnOut = some ⟨Delta, hleft⟩

/--
Type-level support for a chosen left profile.

This carries the same information as `SeqLeftProfileCompatibleCI`, but as
Type-level payloads.  It is needed when constructing a `SeqLeftRootScaffoldCI`,
which itself lives in `Type`.
-/
structure SeqLeftProfileSupportCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (_D : SeqStaticDecompositionCI hentry)
    (P : BodyControlProfile Γ s) : Type where
  normalFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      SeqLeftNormalPayloadCI P
  returnFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
        Sum
          (SeqLeftReturnPayloadCI P)
          (SeqLeftNormalPayloadCI P)

namespace SeqLeftProfileSupportCI

/-- Forget the Type-level support to the Prop-level compatibility statement. -/
theorem toCompatible
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {P : BodyControlProfile Γ s}
    (S : SeqLeftProfileSupportCI hentry D P) :
    SeqLeftProfileCompatibleCI hentry D P := by
  refine
    { normalFromWhole := ?_
      returnFromWhole := ?_ }
  · intro out hout
    let hnorm := S.normalFromWhole hout
    exact ⟨hnorm.Θ, hnorm.hleft, hnorm.hprofile⟩
  · intro out hout
    cases S.returnFromWhole hout with
    | inl hret =>
        exact Or.inl ⟨hret.Delta, hret.hleft, hret.hprofile⟩
    | inr hnorm =>
        exact Or.inr ⟨hnorm.Θ, hnorm.hleft, hnorm.hprofile⟩

end SeqLeftProfileSupportCI

/--
Root/coherence package for a chosen left profile.

This is separated from profile selection.  The profile says which left channels
are exposed; the root chooses one available entry witness and proves coherence
with that profile.
-/
structure SeqLeftRootScaffoldCI
    (Γ : TypeEnv) (s : CppStmt)
    (P : BodyControlProfile Γ s) : Type where
  root : BodyEntryWitness Γ s
  rootCoherent : BodyRootCoherent P root

/--
Compatibility condition for a chosen full left static scaffold.

This is now only a wrapper around profile compatibility.  Root coherence is
carried by `SeqLeftRootScaffoldCI` and then by `SeqLeftStaticScaffoldCI` itself.
-/
structure SeqLeftStaticScaffoldCompatibleCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (S : SeqLeftStaticScaffoldCI Γ s) : Prop where
  profileCompatible :
    SeqLeftProfileCompatibleCI hentry D S.profile

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
Type-level package selecting a left profile together with Type-level support.

This cannot be a subtype `{ P // SeqLeftProfileSupportCI ... P }`, because
`SeqLeftProfileSupportCI ... P` lives in `Type`, not `Prop`.
-/
structure SeqLeftProfilePayloadCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) : Type where
  profile : BodyControlProfile Γ s
  support : SeqLeftProfileSupportCI hentry D profile

/--
A Type-level normal slot for the extracted left profile.
-/
structure SeqLeftNormalSlotCI
    (Γ : TypeEnv) (s : CppStmt) : Type where
  Θ : TypeEnv
  hleft : HasTypeStmtCI .normalK Γ s Θ

namespace SeqLeftNormalSlotCI

def out
    {Γ : TypeEnv} {s : CppStmt}
    (n : SeqLeftNormalSlotCI Γ s) :
    {Δ : TypeEnv // HasTypeStmtCI .normalK Γ s Δ} :=
  ⟨n.Θ, n.hleft⟩

end SeqLeftNormalSlotCI

/--
A Type-level return slot for the extracted left profile.
-/
structure SeqLeftReturnSlotCI
    (Γ : TypeEnv) (s : CppStmt) : Type where
  Δ : TypeEnv
  hleft : HasTypeStmtCI .returnK Γ s Δ

namespace SeqLeftReturnSlotCI

def out
    {Γ : TypeEnv} {s : CppStmt}
    (r : SeqLeftReturnSlotCI Γ s) :
    {Δ : TypeEnv // HasTypeStmtCI .returnK Γ s Δ} :=
  ⟨r.Δ, r.hleft⟩

end SeqLeftReturnSlotCI

/--
Slot-level profile selection for the left side of a sequence.

This is narrower than selecting an arbitrary `BodyControlProfile`.  A statement
body profile is just a normal slot and a return slot, so the real remaining
static choice is exactly which two optional slots are selected.

The support fields are Type-level, not Prop-level.  This is necessary because
`toSupport` constructs `SeqLeftProfileSupportCI`, which lives in `Type`.
-/
structure SeqLeftProfileSlotPayloadCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (_D : SeqStaticDecompositionCI hentry) : Type where
  normalSlot : Option (SeqLeftNormalSlotCI Γ s)
  returnSlot : Option (SeqLeftReturnSlotCI Γ s)
  normalFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      { n : SeqLeftNormalSlotCI Γ s // normalSlot = some n }
  returnFromWhole :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
        Sum
          ({ r : SeqLeftReturnSlotCI Γ s // returnSlot = some r })
          ({ n : SeqLeftNormalSlotCI Γ s // normalSlot = some n })

namespace SeqLeftProfileSlotPayloadCI

/-- Convert selected slots into the actual left control profile. -/
def toProfile
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (S : SeqLeftProfileSlotPayloadCI hentry D) :
    BodyControlProfile Γ s :=
  { summary :=
      { normalOut := S.normalSlot.map (fun n => n.out)
        returnOut := S.returnSlot.map (fun r => r.out) } }

/--
The Type-level support induced by the selected slots.

This is the bridge from slot-level selection to the existing support interface.
Because `normalFromWhole` and `returnFromWhole` are Type-level fields, this
definition does not eliminate Prop into Type.
-/
def toSupport
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (S : SeqLeftProfileSlotPayloadCI hentry D) :
    SeqLeftProfileSupportCI hentry D S.toProfile := by
  refine
    { normalFromWhole := ?_
      returnFromWhole := ?_ }
  · intro out hout
    rcases S.normalFromWhole hout with ⟨n, hn⟩
    exact
      { Θ := n.Θ
        hleft := n.hleft
        hprofile := by
          simp [toProfile, hn, SeqLeftNormalSlotCI.out] }
  · intro out hout
    cases S.returnFromWhole hout with
    | inl hret =>
        rcases hret with ⟨r, hr⟩
        exact
          Sum.inl
            { Delta := r.Δ
              hleft := r.hleft
              hprofile := by
                simp [toProfile, hr, SeqLeftReturnSlotCI.out] }
    | inr hnorm =>
        rcases hnorm with ⟨n, hn⟩
        exact
          Sum.inr
            { Θ := n.Θ
              hleft := n.hleft
              hprofile := by
                simp [toProfile, hn, SeqLeftNormalSlotCI.out] }

end SeqLeftProfileSlotPayloadCI

/--
Type-level decision for a visible whole-sequence normal channel.

A whole-sequence normal channel is possible only through `seq_normal`, so the
left side must expose the same left-normal witness as the selected normal slot.

This is stronger than merely saying that some normal slot exists.
-/
inductive SeqNormalSlotDecisionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (normalSlot : Option (SeqLeftNormalSlotCI Γ s))
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}) : Type where
  | normal
      {Θ Δ : TypeEnv}
      (hleft : HasTypeStmtCI .normalK Γ s Θ)
      (htail : HasTypeStmtCI .normalK Θ t Δ)
      (houtDef : out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩)
      (hslot : normalSlot = some ⟨Θ, hleft⟩) :
      SeqNormalSlotDecisionCI normalSlot out

namespace SeqNormalSlotDecisionCI

/-- Forget the Type-level normal decision to Prop-level normal-source provenance. -/
theorem toProp
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {normalSlot : Option (SeqLeftNormalSlotCI Γ s)}
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}}
    (d : SeqNormalSlotDecisionCI (hentry := hentry) (D := D) normalSlot out) :
    SeqNormalSourceCI out := by
  cases d with
  | normal hleft htail houtDef hslot =>
      exact SeqNormalSourceCI.normal hleft htail houtDef

/-- Forget the Type-level normal decision to the old selected-slot shape. -/
def toSelectedSlot
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {normalSlot : Option (SeqLeftNormalSlotCI Γ s)}
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}}
    (d : SeqNormalSlotDecisionCI (hentry := hentry) (D := D) normalSlot out) :
    { n : SeqLeftNormalSlotCI Γ s // normalSlot = some n } := by
  cases d with
  | normal hleft htail houtDef hslot =>
      exact ⟨⟨_, hleft⟩, hslot⟩

end SeqNormalSlotDecisionCI

/--
Normal-slot selection for the left side of a sequence.

For each visible whole-sequence normal channel, we choose a Type-level decision
showing that the selected normal slot is exactly the left-normal witness used by
that `seq_normal` source.
-/
structure SeqLeftNormalSlotSelectionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) : Type where
  normalSlot : Option (SeqLeftNormalSlotCI Γ s)
  normalDecision :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      SeqNormalSlotDecisionCI (hentry := hentry) (D := D) normalSlot out

namespace SeqLeftNormalSlotSelectionCI

/--
Compatibility projection for callers that only need the old selected-slot shape.
-/
def normalFromWhole
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}}
    (hout : hentry.static.profile.summary.normalOut = some out) :
    { n : SeqLeftNormalSlotCI Γ s // N.normalSlot = some n } :=
  (N.normalDecision hout).toSelectedSlot

/--
The Type-level normal decision is compatible with the Prop-level decomposition.
-/
theorem normalDecision_toProp
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}}
    (hout : hentry.static.profile.summary.normalOut = some out) :
    SeqNormalSourceCI out :=
  (N.normalDecision hout).toProp

end SeqLeftNormalSlotSelectionCI

/--
Type-level decision for a visible whole-sequence return channel.

This is the only Type-level return provenance used by the left-profile
selection layer.  It combines the return-source provenance with the slot proof
required by that source:
- a left-originated return carries the matching selected left return slot;
- a tail-originated return carries the matching selected left normal slot.

The matching is important: the tail-return branch must not merely prove that
some normal slot exists.  It must prove that the selected normal slot is the one
corresponding to the `hleft` witness in the tail-return source.
-/
inductive SeqReturnSlotDecisionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (returnSlot : Option (SeqLeftReturnSlotCI Γ s))
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}) : Type where
  | leftReturn
      {Δ : TypeEnv}
      (hleft : HasTypeStmtCI .returnK Γ s Δ)
      (houtDef : out = ⟨Δ, HasTypeStmtCI.seq_return hleft⟩)
      (hslot : returnSlot = some ⟨Δ, hleft⟩) :
      SeqReturnSlotDecisionCI N returnSlot out
  | tailReturn
      {Θ Δ : TypeEnv}
      (hleft : HasTypeStmtCI .normalK Γ s Θ)
      (htail : HasTypeStmtCI .returnK Θ t Δ)
      (houtDef : out = ⟨Δ, HasTypeStmtCI.seq_normal hleft htail⟩)
      (hslot : N.normalSlot = some ⟨Θ, hleft⟩) :
      SeqReturnSlotDecisionCI N returnSlot out

namespace SeqReturnSlotDecisionCI

/-- Forget the Type-level decision to Prop-level return-source provenance. -/
theorem toProp
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {returnSlot : Option (SeqLeftReturnSlotCI Γ s)}
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}}
    (d : SeqReturnSlotDecisionCI N returnSlot out) :
    SeqReturnSourceCI out := by
  cases d with
  | leftReturn hleft houtDef hslot =>
      exact SeqReturnSourceCI.leftReturn hleft houtDef
  | tailReturn hleft htail houtDef hslot =>
      exact SeqReturnSourceCI.tailReturn hleft htail houtDef

/-- Forget the Type-level decision to the old slot-dispatcher shape. -/
def toSum
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {returnSlot : Option (SeqLeftReturnSlotCI Γ s)}
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}}
    (d : SeqReturnSlotDecisionCI N returnSlot out) :
    Sum
      ({ r : SeqLeftReturnSlotCI Γ s // returnSlot = some r })
      ({ n : SeqLeftNormalSlotCI Γ s // N.normalSlot = some n }) := by
  cases d with
  | leftReturn hleft houtDef hslot =>
      exact Sum.inl ⟨⟨_, hleft⟩, hslot⟩
  | tailReturn hleft htail houtDef hslot =>
      exact Sum.inr ⟨⟨_, hleft⟩, hslot⟩

end SeqReturnSlotDecisionCI

/--
Return-slot selection for the left side of a sequence, relative to the already
chosen normal slot.

For each visible whole-sequence return channel, we choose a Type-level decision:
either it is a left-return channel covered by a left return slot, or it is a
tail-return channel covered by the already selected left normal slot.
-/
structure SeqLeftReturnSlotSelectionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D) : Type where
  returnSlot : Option (SeqLeftReturnSlotCI Γ s)
  returnDecision :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
      SeqReturnSlotDecisionCI N returnSlot out

namespace SeqLeftReturnSlotSelectionCI

/--
Compatibility projection for callers that only need the old dispatcher shape.
-/
def returnFromWhole
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    (R : SeqLeftReturnSlotSelectionCI hentry D N)
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}}
    (hout : hentry.static.profile.summary.returnOut = some out) :
    Sum
      ({ r : SeqLeftReturnSlotCI Γ s // R.returnSlot = some r })
      ({ n : SeqLeftNormalSlotCI Γ s // N.normalSlot = some n }) :=
  (R.returnDecision hout).toSum

/--
The Type-level return decision is compatible with the Prop-level decomposition.
-/
theorem returnDecision_toProp
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    (R : SeqLeftReturnSlotSelectionCI hentry D N)
    {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}}
    (hout : hentry.static.profile.summary.returnOut = some out) :
    SeqReturnSourceCI out :=
  (R.returnDecision hout).toProp

end SeqLeftReturnSlotSelectionCI

namespace SeqLeftProfileSlotPayloadCI

/--
Assemble the old slot payload from separated, source-aware normal-slot and
return-slot selections.
-/
def ofSelections
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (R : SeqLeftReturnSlotSelectionCI hentry D N) :
    SeqLeftProfileSlotPayloadCI hentry D :=
  { normalSlot := N.normalSlot
    returnSlot := R.returnSlot
    normalFromWhole := by
      intro out hout
      exact N.normalFromWhole hout
    returnFromWhole := by
      intro out hout
      exact R.returnFromWhole hout }

end SeqLeftProfileSlotPayloadCI

/--
Remaining normal-slot selection obligation for the left side of a sequence.

This is now separated from return-slot selection.  The normal slot is the
critical slot used both by whole-sequence normal execution and by tail-originated
returns.
-/
axiom seq_left_normal_slot_selection_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) :
    SeqLeftNormalSlotSelectionCI hentry D

/--
Remaining return-slot selection obligation for the left side of a sequence,
relative to the chosen normal slot.

This is deliberately relative to `N`: tail-originated returns must point back to
the same selected left normal slot, not an unrelated normal witness.
-/
axiom seq_left_return_slot_selection_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D) :
    SeqLeftReturnSlotSelectionCI hentry D N

/--
Compatibility name for the previous profile-slot payload.

The payload is now assembled from separately selected normal and return slots.
-/
noncomputable def seq_left_profile_slots_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) :
    SeqLeftProfileSlotPayloadCI hentry D :=
  let N := seq_left_normal_slot_selection_ci_of_decomposition hentry D
  let R := seq_left_return_slot_selection_ci_of_decomposition hentry D N
  SeqLeftProfileSlotPayloadCI.ofSelections N R

/--
Compatibility package selecting a left profile together with Type-level support.

This is now assembled from slot-level selection rather than postulating an
arbitrary profile directly.
-/
noncomputable def seq_left_profile_payload_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) :
    SeqLeftProfilePayloadCI hentry D :=
  let S := seq_left_profile_slots_ci_of_decomposition hentry D
  { profile := S.toProfile
    support := S.toSupport }

/--
Root/coherence for a chosen left profile is definitionally assembled from
Type-level profile support.

This cannot be proved from `SeqLeftProfileCompatibleCI : Prop`, because that
would require eliminating Prop-level `Exists`/`Or` into `Type`.
-/
def seq_left_root_scaffold_ci_of_profile
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (P : BodyControlProfile Γ s)
    (S : SeqLeftProfileSupportCI hentry D P) :
    SeqLeftRootScaffoldCI Γ s P := by
  cases hroot : hentry.static.root with
  | normal out =>
      have hN :
          hentry.static.profile.summary.normalOut = some out := by
        simpa [hroot] using
          (BodyStaticBoundaryCI.root_normal_coherent hentry.static)
      let hnorm := S.normalFromWhole hN
      exact
        { root := .normal ⟨hnorm.Θ, hnorm.hleft⟩
          rootCoherent := BodyRootCoherent.normal hnorm.hprofile }
  | returned out =>
      have hR :
          hentry.static.profile.summary.returnOut = some out := by
        simpa [hroot] using
          (BodyStaticBoundaryCI.root_return_coherent hentry.static)
      cases S.returnFromWhole hR with
      | inl hret =>
          exact
            { root := .returned ⟨hret.Delta, hret.hleft⟩
              rootCoherent := BodyRootCoherent.returned hret.hprofile }
      | inr hnorm =>
          exact
            { root := .normal ⟨hnorm.Θ, hnorm.hleft⟩
              rootCoherent := BodyRootCoherent.normal hnorm.hprofile }

/--
Assemble the full left static scaffold from separately chosen profile and root
packages.

The remaining static assumption is now only profile selection with Type-level
support.  Root/coherence is definitionally assembled from that support.
-/
noncomputable def seq_left_static_scaffold_payload_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) :
    { S : SeqLeftStaticScaffoldCI Γ s //
      SeqLeftStaticScaffoldCompatibleCI hentry D S } := by
  let Ppack := seq_left_profile_payload_ci_of_decomposition hentry D
  let R :=
    seq_left_root_scaffold_ci_of_profile
      hentry
      D
      Ppack.profile
      Ppack.support
  refine
    ⟨{ profile := Ppack.profile
       root := R.root
       rootCoherent := R.rootCoherent }, ?_⟩
  exact
    { profileCompatible := Ppack.support.toCompatible }

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

/-- Left static boundary assembled from theorem-backed `typed0` and the static scaffold. -/
noncomputable def seq_left_static_boundary_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStaticBoundaryCI Γ s :=
  (seq_left_static_scaffold_ci_of_entry hentry).toBodyStaticBoundaryCI
    (seq_left_typed0_of_entry hentry)



/--
Normal-channel adequacy obligation for the tail after an actual left-normal
route.

This mirrors the left-side channel split.  Tail adequacy is path-sensitive, so
its support is indexed by the actual post-environment and post-state reached by
the left-normal execution.
-/
structure SeqTailNormalAdequacyCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt)
    (P : BodyControlProfile Θ t) : Type where
  normalSound :
    ∀ {σ2 : State} (_hstep : BigStepStmt σ1 t .normal σ2),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Θ t Δ},
        P.summary.normalOut = some out

/--
Return-channel adequacy obligation for the tail after an actual left-normal
route.
-/
structure SeqTailReturnAdequacyCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt)
    (P : BodyControlProfile Θ t) : Type where
  returnSound :
    ∀ {rv : Option Value} {σ2 : State}
      (_hstep : BigStepStmt σ1 t (.returnResult rv) σ2),
      ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Θ t Δ},
        P.summary.returnOut = some out

/-- Type-level package for the two semantic adequacy channels of the tail. -/
structure SeqTailAdequacySupportCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt)
    (P : BodyControlProfile Θ t) : Type where
  normal : SeqTailNormalAdequacyCI Θ σ1 t P
  returned : SeqTailReturnAdequacyCI Θ σ1 t P

namespace SeqTailAdequacySupportCI

/-- Forget the channel-split tail support to ordinary `BodyAdequacyCI`. -/
noncomputable def toBodyAdequacyCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    {P : BodyControlProfile Θ t}
    (A : SeqTailAdequacySupportCI Θ σ1 t P) :
    BodyAdequacyCI Θ σ1 t P :=
  BodyAdequacyCI.ofWitness
    (normalWitness := by
      intro σ2 hstep
      let h := A.normal.normalSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩)
    (returnWitness := by
      intro rv σ2 hstep
      let h := A.returned.returnSound hstep
      exact ⟨Classical.choose h, Classical.choose_spec h⟩)

end SeqTailAdequacySupportCI

/--
Type-level package selecting the tail static boundary together with channel-split
tail adequacy support after an actual left-normal route.
-/
structure SeqTailStaticAdequacyPayloadCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  static : BodyStaticBoundaryCI Θ t
  support : SeqTailAdequacySupportCI Θ σ1 t static.profile

/-- Compatibility package for the older tail scaffold API. -/
noncomputable def SeqTailStaticAdequacyPayloadCI.toStaticAdequacyCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    (p : SeqTailStaticAdequacyPayloadCI Θ σ1 t) :
    SeqTailStaticAdequacyCI Θ σ1 t :=
  { static := p.static
    adequacy := p.support.toBodyAdequacyCI }

/--
Actual head-normal route through a sequence.

This is the route-aware replacement for passing around a bare
`HasTypeStmtCI .normalK Γ s Θ` and an unrelated normal step.  The package
records the selected left normal witness, the actual head-normal execution, the
fact that the chosen left profile exposes that witness, and the tail
static/adequacy payload for the resulting post-state.
-/
structure SeqHeadNormalRouteCI
    (Γ : TypeEnv) (σ : State) (s t : CppStmt)
    (σ1 : State) (P : BodyControlProfile Γ s) : Type where
  Θ : TypeEnv
  hleft : HasTypeStmtCI .normalK Γ s Θ
  hprofile : P.summary.normalOut = some ⟨Θ, hleft⟩
  hstepLeft : BigStepStmt σ s .normal σ1
  tail : SeqTailStaticAdequacyPayloadCI Θ σ1 t

end Cpp
