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
import CppFormalization.Cpp2.Closure.Foundation.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

abbrev FunctionBodyClosureResult (σ : State) (st : CppStmt) : Prop :=
  (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st

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
def toBodyAdequacyCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    {P : BodyControlProfile Θ t}
    (A : SeqTailAdequacySupportCI Θ σ1 t P) :
    BodyAdequacyCI Θ σ1 t P :=
  { normalSound := A.normal.normalSound
    returnSound := A.returned.returnSound }

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
def SeqTailStaticAdequacyPayloadCI.toStaticAdequacyCI
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
  { normalSound := by
      intro σ1 hstep
      let r := A.normal.normalRoute hstep
      exact ⟨⟨r.Θ, r.hleft⟩, r.hprofile⟩
    returnSound := by
      intro rv σ' hstep
      exact (A.returned.returnDecision hstep).toExists }

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
def seq_left_adequacy_ci_of_entry
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
  { structural := seq_left_structural_boundary_of_entry hentry
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
def seq_tail_static_adequacy_ci_of_head_normal_route
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
    { structural := seq_tail_structural_boundary_of_entry hentry
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
  { structural := seq_tail_structural_boundary_of_entry hentry
    static := route.tail.static
    adequacy := route.tail.support.toBodyAdequacyCI }

/--
Tail closure boundary extracted from a selected head-normal route.

This is the preferred route-aware replacement for the older
`seq_tail_closure_boundary_ci_of_left_normal` path.
-/
noncomputable def seq_tail_closure_boundary_ci_of_head_normal_route
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) :
    BodyClosureBoundaryCI route.Θ σ1 t := by
  have hreadyLeft : StmtReadyConcrete Γ σ s :=
    seq_ready_left hentry.dynamic.safe
  have hσ1 : ScopedTypedStateConcrete route.Θ σ1 :=
    stmt_normal_preserves_scoped_typed_state_concrete
      mkWhileReentry route.hleft hentry.dynamic.state hreadyLeft route.hstepLeft
  have hreadyRight : StmtReadyConcrete route.Θ σ1 t :=
    seq_ready_right_after_left_normal route.hleft hσ1 hentry.dynamic.safe route.hstepLeft
  let hs := seq_tail_closure_scaffold_ci_of_head_normal_route hentry route
  let hd : BodyDynamicBoundary route.Θ σ1 t :=
    { state := hσ1
      safe := hreadyRight }
  exact mkBodyClosureBoundaryCI hs.structural hs.static hd hs.adequacy


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
Route-aware theorem version of the seq shell.

The tail is invoked only with the selected head-normal route supplied by the
left adequacy support.  This avoids treating an arbitrary normal witness as a
valid tail continuation route.
-/
theorem seq_function_body_closure_boundary_ci_honest
    (mkWhileReentry : WhileReentryReadyProvider)
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
  have hleft : FunctionBodyClosureResult σ s :=
    leftClosure (seq_left_closure_boundary_ci_of_entry hentry)
  exact
    seq_function_body_result_return_aware
      hleft
      (fun hstep =>
        let route := seq_left_normalRoute_of_entry hentry hstep
        let htailBoundary :=
          seq_tail_closure_boundary_ci_of_head_normal_route
            mkWhileReentry hentry route
        tailClosure route htailBoundary)

/-!
## Ite branch boundary extraction

Unlike `seq`, `ite` does not enter a tail through a post-state/post-environment
computed by the head statement.  Both branches are entered from the original
state and environment.  Therefore structural and dynamic branch boundaries are
theorem-backed projections from the whole `ite` boundary; the remaining debt is
branch static and branch adequacy.
-/

/-- Condition readiness extracted from a concrete `ite` readiness package. -/
theorem ite_ready_cond
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    ExprReadyConcrete Γ σ c (.base .bool) := by
  intro h
  cases h with
  | ite _ hcond _ _ =>
      exact hcond

/-- Then-branch readiness extracted from a concrete `ite` readiness package. -/
theorem ite_ready_then
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    StmtReadyConcrete Γ σ s := by
  intro h
  cases h with
  | ite _ _ hthen _ =>
      exact hthen

/-- Else-branch readiness extracted from a concrete `ite` readiness package. -/
theorem ite_ready_else
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    StmtReadyConcrete Γ σ t := by
  intro h
  cases h with
  | ite _ _ _ helse =>
      exact helse

/--
Then-branch structural boundary projected from the whole `ite` boundary.

This is theorem-backed because `WellFormedStmt`, `BreakWellScoped`, and
`ContinueWellScoped` all decompose structurally over `ite`.
-/
theorem ite_then_structural_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStructuralBoundary Γ s := by
  have hwf : WellFormedValue c ∧ WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.2.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/--
Else-branch structural boundary projected from the whole `ite` boundary.

This is theorem-backed because `WellFormedStmt`, `BreakWellScoped`, and
`ContinueWellScoped` all decompose structurally over `ite`.
-/
theorem ite_else_structural_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStructuralBoundary Γ t := by
  have hwf : WellFormedValue c ∧ WellFormedStmt s ∧ WellFormedStmt t := by
    simpa [WellFormedStmt] using hentry.structural.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScoped t := by
    simpa [BreakWellScoped] using hentry.structural.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScoped t := by
    simpa [ContinueWellScoped] using hentry.structural.continueScoped
  exact
    { wf := hwf.2.2
      breakScoped := hbreak.2
      continueScoped := hcont.2 }

/--
Dynamic boundary for the then branch of an `ite`.

The branch starts in the same state as the whole `ite`; the branch readiness is
a direct projection of `StmtReadyConcrete.ite`.
-/
def ite_then_dynamic_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyDynamicBoundary Γ σ s :=
  { state := hentry.dynamic.state
    safe := ite_ready_then hentry.dynamic.safe }

/--
Dynamic boundary for the else branch of an `ite`.

The branch starts in the same state as the whole `ite`; the branch readiness is
a direct projection of `StmtReadyConcrete.ite`.
-/
def ite_else_dynamic_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyDynamicBoundary Γ σ t :=
  { state := hentry.dynamic.state
    safe := ite_ready_else hentry.dynamic.safe }

/--
Type-level root payload for a selected branch profile.

This is the small piece of data needed to define the branch root and its
coherence proof without keeping root/coherence as an axiom field.
-/
inductive IteBranchRootPayloadCI
    {Γ : TypeEnv} {st : CppStmt}
    (profile : BodyControlProfile Γ st) : Type where
  | normal
      {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ}}
      (hprofile : profile.summary.normalOut = some out) :
      IteBranchRootPayloadCI profile
  | returned
      {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ}}
      (hprofile : profile.summary.returnOut = some out) :
      IteBranchRootPayloadCI profile

namespace IteBranchRootPayloadCI

/-- The branch entry witness determined by a root payload. -/
def toRoot
    {Γ : TypeEnv} {st : CppStmt}
    {profile : BodyControlProfile Γ st}
    (p : IteBranchRootPayloadCI profile) :
    BodyEntryWitness Γ st :=
  match p with
  | .normal (out := out) _ => .normal out
  | .returned (out := out) _ => .returned out

/-- Root coherence is definitionally induced by the root payload. -/
theorem toRootCoherent
    {Γ : TypeEnv} {st : CppStmt}
    {profile : BodyControlProfile Γ st}
    (p : IteBranchRootPayloadCI profile) :
    BodyRootCoherent profile p.toRoot := by
  cases p with
  | normal hprofile =>
      exact BodyRootCoherent.normal hprofile
  | returned hprofile =>
      exact BodyRootCoherent.returned hprofile

end IteBranchRootPayloadCI

/--
A Type-level normal slot for an extracted `ite` branch profile.
-/
structure IteBranchNormalSlotCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  Δ : TypeEnv
  hty : HasTypeStmtCI .normalK Γ st Δ

namespace IteBranchNormalSlotCI

def out
    {Γ : TypeEnv} {st : CppStmt}
    (n : IteBranchNormalSlotCI Γ st) :
    {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ} :=
  ⟨n.Δ, n.hty⟩

end IteBranchNormalSlotCI

/--
A Type-level return slot for an extracted `ite` branch profile.
-/
structure IteBranchReturnSlotCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  Δ : TypeEnv
  hty : HasTypeStmtCI .returnK Γ st Δ

namespace IteBranchReturnSlotCI

def out
    {Γ : TypeEnv} {st : CppStmt}
    (r : IteBranchReturnSlotCI Γ st) :
    {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ} :=
  ⟨r.Δ, r.hty⟩

end IteBranchReturnSlotCI

/--
Slot-level profile payload for one branch of an `ite`.

A branch profile is just an optional normal slot and an optional return slot.
The root is not an independent field: it is chosen from one of the selected
slots, and the old root/coherence payload is derived by definition below.
-/
structure IteBranchProfileSlotPayloadCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  normalSlot : Option (IteBranchNormalSlotCI Γ st)
  returnSlot : Option (IteBranchReturnSlotCI Γ st)
  rootChoice :
    Sum
      ({ n : IteBranchNormalSlotCI Γ st // normalSlot = some n })
      ({ r : IteBranchReturnSlotCI Γ st // returnSlot = some r })

namespace IteBranchProfileSlotPayloadCI

/-- Convert selected branch slots into the actual branch control profile. -/
def toProfile
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st) :
    BodyControlProfile Γ st :=
  { summary :=
      { normalOut := S.normalSlot.map (fun n => IteBranchNormalSlotCI.out n)
        returnOut := S.returnSlot.map (fun r => IteBranchReturnSlotCI.out r) } }

/--
The root payload induced by the selected root slot.

This is the branch analogue of the seq slot-to-profile bridge: once the branch
slots and root choice are selected, root/coherence is definitional.
-/
def toRootPayload
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st) :
    IteBranchRootPayloadCI S.toProfile := by
  cases S.rootChoice with
  | inl hn =>
      rcases hn with ⟨n, hn⟩
      exact
        IteBranchRootPayloadCI.normal
          (out := IteBranchNormalSlotCI.out n)
          (by simp [toProfile, hn, IteBranchNormalSlotCI.out])
  | inr hr =>
      rcases hr with ⟨r, hr⟩
      exact
        IteBranchRootPayloadCI.returned
          (out := IteBranchReturnSlotCI.out r)
          (by simp [toProfile, hr, IteBranchReturnSlotCI.out])

end IteBranchProfileSlotPayloadCI

/--
Normal channel provenance for a whole `ite` payload.

A whole `ite` exposes a normal channel only when both branches expose the same
normal post-environment.  The condition typing is kept in the source because it
is part of the `HasTypeStmtCI.ite` constructor.
-/
inductive IteNormalSourceCI
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Δ}) : Prop where
  | normal
      {Δ : TypeEnv}
      (hcond : HasValueType Γ c (.base .bool))
      (hthen : HasTypeStmtCI .normalK Γ s Δ)
      (helse : HasTypeStmtCI .normalK Γ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.ite hcond hthen helse⟩) :
      IteNormalSourceCI out

/--
Return channel provenance for a whole `ite` payload.

A whole `ite` exposes a return channel only when both branches expose the same
return post-environment.
-/
inductive IteReturnSourceCI
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.ite c s t) Δ}) : Prop where
  | returned
      {Δ : TypeEnv}
      (hcond : HasValueType Γ c (.base .bool))
      (hthen : HasTypeStmtCI .returnK Γ s Δ)
      (helse : HasTypeStmtCI .returnK Γ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.ite hcond hthen helse⟩) :
      IteReturnSourceCI out

theorem ite_normal_source_ci_of_out
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Δ}) :
    IteNormalSourceCI out := by
  rcases out with ⟨Δ, hty⟩
  cases hty with
  | ite hcond hthen helse =>
      exact IteNormalSourceCI.normal hcond hthen helse rfl

theorem ite_return_source_ci_of_out
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.ite c s t) Δ}) :
    IteReturnSourceCI out := by
  rcases out with ⟨Δ, hty⟩
  cases hty with
  | ite hcond hthen helse =>
      exact IteReturnSourceCI.returned hcond hthen helse rfl

/--
Type-level decision connecting a whole `ite` normal channel to the selected
then-branch normal slot.
-/
inductive IteThenNormalSlotDecisionCI
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (normalSlot : Option (IteBranchNormalSlotCI Γ s))
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Δ}) : Type where
  | normal
      {Δ : TypeEnv}
      (hcond : HasValueType Γ c (.base .bool))
      (hthen : HasTypeStmtCI .normalK Γ s Δ)
      (helse : HasTypeStmtCI .normalK Γ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.ite hcond hthen helse⟩)
      (hslot : normalSlot = some ⟨Δ, hthen⟩) :
      IteThenNormalSlotDecisionCI normalSlot out

/--
Type-level decision connecting a whole `ite` normal channel to the selected
else-branch normal slot.
-/
inductive IteElseNormalSlotDecisionCI
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (normalSlot : Option (IteBranchNormalSlotCI Γ t))
    (out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Δ}) : Type where
  | normal
      {Δ : TypeEnv}
      (hcond : HasValueType Γ c (.base .bool))
      (hthen : HasTypeStmtCI .normalK Γ s Δ)
      (helse : HasTypeStmtCI .normalK Γ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.ite hcond hthen helse⟩)
      (hslot : normalSlot = some ⟨Δ, helse⟩) :
      IteElseNormalSlotDecisionCI normalSlot out

/--
Type-level decision connecting a whole `ite` return channel to the selected
then-branch return slot.
-/
inductive IteThenReturnSlotDecisionCI
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (returnSlot : Option (IteBranchReturnSlotCI Γ s))
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.ite c s t) Δ}) : Type where
  | returned
      {Δ : TypeEnv}
      (hcond : HasValueType Γ c (.base .bool))
      (hthen : HasTypeStmtCI .returnK Γ s Δ)
      (helse : HasTypeStmtCI .returnK Γ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.ite hcond hthen helse⟩)
      (hslot : returnSlot = some ⟨Δ, hthen⟩) :
      IteThenReturnSlotDecisionCI returnSlot out

/--
Type-level decision connecting a whole `ite` return channel to the selected
else-branch return slot.
-/
inductive IteElseReturnSlotDecisionCI
    {Γ : TypeEnv} {c : ValExpr} {s t : CppStmt}
    (returnSlot : Option (IteBranchReturnSlotCI Γ t))
    (out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.ite c s t) Δ}) : Type where
  | returned
      {Δ : TypeEnv}
      (hcond : HasValueType Γ c (.base .bool))
      (hthen : HasTypeStmtCI .returnK Γ s Δ)
      (helse : HasTypeStmtCI .returnK Γ t Δ)
      (hout : out = ⟨Δ, HasTypeStmtCI.ite hcond hthen helse⟩)
      (hslot : returnSlot = some ⟨Δ, helse⟩) :
      IteElseReturnSlotDecisionCI returnSlot out

/--
Canonical slot-level profile payload for the then branch of an `ite`.

The payload is no longer merely branch-local: every visible whole-`ite` normal
or return channel is connected to the corresponding selected branch slot.
-/
structure IteThenProfileSlotPayloadCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) : Type where
  branch : IteBranchProfileSlotPayloadCI Γ s
  normalDecision :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      IteThenNormalSlotDecisionCI branch.normalSlot out
  returnDecision :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.ite c s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
      IteThenReturnSlotDecisionCI branch.returnSlot out

/--
Canonical slot-level profile payload for the else branch of an `ite`.
-/
structure IteElseProfileSlotPayloadCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) : Type where
  branch : IteBranchProfileSlotPayloadCI Γ t
  normalDecision :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.ite c s t) Δ}},
      hentry.static.profile.summary.normalOut = some out →
      IteElseNormalSlotDecisionCI branch.normalSlot out
  returnDecision :
    ∀ {out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.ite c s t) Δ}},
      hentry.static.profile.summary.returnOut = some out →
      IteElseReturnSlotDecisionCI branch.returnSlot out

/--
Profile payload for one branch of an `ite`.

The remaining static choice is now explicit: choose a branch profile, and choose
one available root payload for that profile.  The root witness and coherence
record are derived from this payload by definitions below.
-/
structure IteBranchProfilePayloadCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  profile : BodyControlProfile Γ st
  rootPayload : IteBranchRootPayloadCI profile

namespace IteBranchProfilePayloadCI

/-- Build the old profile payload shape from the canonical slot-level payload. -/
def ofSlotPayload
    {Γ : TypeEnv} {st : CppStmt}
    (S : IteBranchProfileSlotPayloadCI Γ st) :
    IteBranchProfilePayloadCI Γ st :=
  { profile := S.toProfile
    rootPayload := S.toRootPayload }

end IteBranchProfilePayloadCI

/--
Root/coherence scaffold for a chosen branch profile.

This structure is kept as a readable compatibility package, but it is produced
by `def` from `IteBranchProfilePayloadCI`; it is not an independent axiom.
-/
structure IteBranchRootScaffoldCI
    (Γ : TypeEnv) (st : CppStmt)
    (profile : BodyControlProfile Γ st) : Type where
  root : BodyEntryWitness Γ st
  rootCoherent : BodyRootCoherent profile root

namespace IteBranchRootScaffoldCI

/-- Build branch root/coherence from the selected profile payload. -/
def ofProfilePayload
    {Γ : TypeEnv} {st : CppStmt}
    (P : IteBranchProfilePayloadCI Γ st) :
    IteBranchRootScaffoldCI Γ st P.profile :=
  { root := P.rootPayload.toRoot
    rootCoherent := P.rootPayload.toRootCoherent }

end IteBranchRootScaffoldCI

/--
Static scaffold for one branch of an `ite`, excluding the coarse `typed0`
payload.

The `typed0` field is theorem-backed from the whole `ite` typing below.  The
only primitive remaining static debt is the profile payload.  Root/coherence is
assembled by definition from that payload.
-/
structure IteBranchStaticScaffoldCI
    (Γ : TypeEnv) (st : CppStmt) : Type where
  profilePayload : IteBranchProfilePayloadCI Γ st

namespace IteBranchStaticScaffoldCI

/-- The selected branch profile. -/
def profile
    {Γ : TypeEnv} {st : CppStmt}
    (h : IteBranchStaticScaffoldCI Γ st) :
    BodyControlProfile Γ st :=
  h.profilePayload.profile

/-- The branch root/coherence scaffold induced by the selected profile payload. -/
def rootScaffold
    {Γ : TypeEnv} {st : CppStmt}
    (h : IteBranchStaticScaffoldCI Γ st) :
    IteBranchRootScaffoldCI Γ st h.profile :=
  IteBranchRootScaffoldCI.ofProfilePayload h.profilePayload

/-- Assemble a branch static boundary from theorem-backed `typed0`. -/
def toBodyStaticBoundaryCI
    {Γ : TypeEnv} {st : CppStmt}
    (h : IteBranchStaticScaffoldCI Γ st)
    (htyped : WellTypedFrom Γ st) :
    BodyStaticBoundaryCI Γ st :=
  { typed0 := htyped
    profile := h.profile
    root := h.rootScaffold.root
    rootCoherent := h.rootScaffold.rootCoherent }

end IteBranchStaticScaffoldCI

/--
The then branch of a well-typed `ite` is well typed.

This is theorem-backed from the coarse `typed0` payload of the whole `ite`.
-/
theorem ite_then_typed0_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    WellTypedFrom Γ s := by
  rcases hentry.static.typed0 with ⟨Δ, htyIte⟩
  cases htyIte with
  | ite _ hthen _ =>
      exact ⟨_, hthen⟩

/--
The else branch of a well-typed `ite` is well typed.

This is theorem-backed from the coarse `typed0` payload of the whole `ite`.
-/
theorem ite_else_typed0_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    WellTypedFrom Γ t := by
  rcases hentry.static.typed0 with ⟨Δ, htyIte⟩
  cases htyIte with
  | ite _ _ helse =>
      exact ⟨_, helse⟩

/--
Remaining then-branch slot-level profile payload obligation.

This is narrower than selecting an arbitrary branch profile: the profile is now
assembled from explicit normal/return slots, and the root is chosen from those
selected slots.
-/
axiom ite_then_profile_slot_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteThenProfileSlotPayloadCI hentry

/--
Remaining else-branch slot-level profile payload obligation.

This is narrower than selecting an arbitrary branch profile: the profile is now
assembled from explicit normal/return slots, and the root is chosen from those
selected slots.
-/
axiom ite_else_profile_slot_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteElseProfileSlotPayloadCI hentry

/-- Compatibility profile payload for the then branch. -/
noncomputable def ite_then_profile_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchProfilePayloadCI Γ s :=
  IteBranchProfilePayloadCI.ofSlotPayload
    (ite_then_profile_slot_payload_ci_of_entry hentry).branch

/-- Compatibility profile payload for the else branch. -/
noncomputable def ite_else_profile_payload_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchProfilePayloadCI Γ t :=
  IteBranchProfilePayloadCI.ofSlotPayload
    (ite_else_profile_slot_payload_ci_of_entry hentry).branch

/-- Then-branch root/coherence scaffold induced by the selected profile payload. -/
noncomputable def ite_then_root_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchRootScaffoldCI Γ s
      (ite_then_profile_payload_ci_of_entry hentry).profile :=
  IteBranchRootScaffoldCI.ofProfilePayload
    (ite_then_profile_payload_ci_of_entry hentry)

/-- Else-branch root/coherence scaffold induced by the selected profile payload. -/
noncomputable def ite_else_root_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchRootScaffoldCI Γ t
      (ite_else_profile_payload_ci_of_entry hentry).profile :=
  IteBranchRootScaffoldCI.ofProfilePayload
    (ite_else_profile_payload_ci_of_entry hentry)

/-- Compatibility static scaffold for the then branch. -/
noncomputable def ite_then_static_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticScaffoldCI Γ s :=
  { profilePayload := ite_then_profile_payload_ci_of_entry hentry }

/-- Compatibility static scaffold for the else branch. -/
noncomputable def ite_else_static_scaffold_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticScaffoldCI Γ t :=
  { profilePayload := ite_else_profile_payload_ci_of_entry hentry }

/-- Then-branch static boundary assembled from scaffold plus theorem-backed typing. -/
noncomputable def ite_then_static_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStaticBoundaryCI Γ s :=
  (ite_then_static_scaffold_ci_of_entry hentry).toBodyStaticBoundaryCI
    (ite_then_typed0_of_entry hentry)

/-- Else-branch static boundary assembled from scaffold plus theorem-backed typing. -/
noncomputable def ite_else_static_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyStaticBoundaryCI Γ t :=
  (ite_else_static_scaffold_ci_of_entry hentry).toBodyStaticBoundaryCI
    (ite_else_typed0_of_entry hentry)

/--
Runtime decision for an actual branch-normal execution of an `ite` branch.

This is the branch analogue of the seq left-return runtime decision: an actual
branch execution must be reflected by the selected normal channel in the branch
profile.
-/
structure IteBranchNormalRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st)
    {σ' : State}
    (_hstep : BigStepStmt σ st .normal σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .normalK Γ st Delta
  hprofile : P.summary.normalOut = some ⟨Delta, hty⟩

namespace IteBranchNormalRuntimeDecisionCI

/-- Forget the runtime normal decision to ordinary adequacy evidence. -/
def toExists
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (d : IteBranchNormalRuntimeDecisionCI Γ σ st P hstep) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ st Δ},
      P.summary.normalOut = some out :=
  ⟨⟨d.Delta, d.hty⟩, d.hprofile⟩

end IteBranchNormalRuntimeDecisionCI

/--
Runtime decision for an actual branch-return execution of an `ite` branch.

An actual branch return must be reflected by the selected return channel in the
branch profile.
-/
structure IteBranchReturnRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st)
    {rv : Option Value} {σ' : State}
    (_hstep : BigStepStmt σ st (.returnResult rv) σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .returnK Γ st Delta
  hprofile : P.summary.returnOut = some ⟨Delta, hty⟩

namespace IteBranchReturnRuntimeDecisionCI

/-- Forget the runtime return decision to ordinary adequacy evidence. -/
def toExists
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    {rv : Option Value} {σ' : State}
    {hstep : BigStepStmt σ st (.returnResult rv) σ'}
    (d : IteBranchReturnRuntimeDecisionCI Γ σ st P hstep) :
    ∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ st Δ},
      P.summary.returnOut = some out :=
  ⟨⟨d.Delta, d.hty⟩, d.hprofile⟩

end IteBranchReturnRuntimeDecisionCI

/--
Slot-aware runtime decision for an actual branch-normal execution.

The decision records that the runtime normal typing witness is exactly the
selected normal slot of the branch profile payload, not merely that the induced
profile contains an equal normal output.
-/
structure IteBranchNormalSlotRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {σ' : State}
    (_hstep : BigStepStmt σ st .normal σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .normalK Γ st Delta
  hslot : S.normalSlot = some ⟨Delta, hty⟩

namespace IteBranchNormalSlotRuntimeDecisionCI

/-- Forget the slot-aware runtime decision to the profile-level decision. -/
def toRuntimeDecision
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {S : IteBranchProfileSlotPayloadCI Γ st}
    {σ' : State}
    {hstep : BigStepStmt σ st .normal σ'}
    (d : IteBranchNormalSlotRuntimeDecisionCI Γ σ st S hstep) :
    IteBranchNormalRuntimeDecisionCI Γ σ st S.toProfile hstep :=
  { Delta := d.Delta
    hty := d.hty
    hprofile := by
      simp [IteBranchProfileSlotPayloadCI.toProfile, d.hslot,
        IteBranchNormalSlotCI.out] }

end IteBranchNormalSlotRuntimeDecisionCI

/--
Slot-aware runtime decision for an actual branch-return execution.

The decision records that the runtime return typing witness is exactly the
selected return slot of the branch profile payload.
-/
structure IteBranchReturnSlotRuntimeDecisionCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (S : IteBranchProfileSlotPayloadCI Γ st)
    {rv : Option Value} {σ' : State}
    (_hstep : BigStepStmt σ st (.returnResult rv) σ') : Type where
  Delta : TypeEnv
  hty : HasTypeStmtCI .returnK Γ st Delta
  hslot : S.returnSlot = some ⟨Delta, hty⟩

namespace IteBranchReturnSlotRuntimeDecisionCI

/-- Forget the slot-aware runtime decision to the profile-level decision. -/
def toRuntimeDecision
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {S : IteBranchProfileSlotPayloadCI Γ st}
    {rv : Option Value} {σ' : State}
    {hstep : BigStepStmt σ st (.returnResult rv) σ'}
    (d : IteBranchReturnSlotRuntimeDecisionCI Γ σ st S hstep) :
    IteBranchReturnRuntimeDecisionCI Γ σ st S.toProfile hstep :=
  { Delta := d.Delta
    hty := d.hty
    hprofile := by
      simp [IteBranchProfileSlotPayloadCI.toProfile, d.hslot,
        IteBranchReturnSlotCI.out] }

end IteBranchReturnSlotRuntimeDecisionCI

/--
Runtime-decision adequacy support for one `ite` branch.

This keeps the branch adequacy obligation aligned with the selected branch
profile instead of exposing only ordinary `BodyAdequacyCI` evidence.
-/
structure IteBranchAdequacySupportCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (P : BodyControlProfile Γ st) : Type where
  normalDecision :
    ∀ {σ' : State}
      (hstep : BigStepStmt σ st .normal σ'),
      IteBranchNormalRuntimeDecisionCI Γ σ st P hstep
  returnDecision :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ st (.returnResult rv) σ'),
      IteBranchReturnRuntimeDecisionCI Γ σ st P hstep

namespace IteBranchAdequacySupportCI

/-- Forget runtime-decision support to ordinary `BodyAdequacyCI`. -/
def toBodyAdequacyCI
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {P : BodyControlProfile Γ st}
    (A : IteBranchAdequacySupportCI Γ σ st P) :
    BodyAdequacyCI Γ σ st P :=
  { normalSound := by
      intro σ' hstep
      exact (A.normalDecision hstep).toExists
    returnSound := by
      intro rv σ' hstep
      exact (A.returnDecision hstep).toExists }

end IteBranchAdequacySupportCI

/--
Slot-aware runtime-decision adequacy support for one `ite` branch.

This is the canonical branch adequacy obligation: actual normal/return branch
executions must use the selected normal/return slots of the branch profile
payload.
-/
structure IteBranchSlotAdequacySupportCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt)
    (S : IteBranchProfileSlotPayloadCI Γ st) : Type where
  normalDecision :
    ∀ {σ' : State}
      (hstep : BigStepStmt σ st .normal σ'),
      IteBranchNormalSlotRuntimeDecisionCI Γ σ st S hstep
  returnDecision :
    ∀ {rv : Option Value} {σ' : State}
      (hstep : BigStepStmt σ st (.returnResult rv) σ'),
      IteBranchReturnSlotRuntimeDecisionCI Γ σ st S hstep

namespace IteBranchSlotAdequacySupportCI

/-- Forget slot-aware adequacy support to profile-level adequacy support. -/
def toAdequacySupport
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    {S : IteBranchProfileSlotPayloadCI Γ st}
    (A : IteBranchSlotAdequacySupportCI Γ σ st S) :
    IteBranchAdequacySupportCI Γ σ st S.toProfile :=
  { normalDecision := by
      intro σ' hstep
      exact (A.normalDecision hstep).toRuntimeDecision
    returnDecision := by
      intro rv σ' hstep
      exact (A.returnDecision hstep).toRuntimeDecision }

end IteBranchSlotAdequacySupportCI

/--
Remaining then-branch slot-aware runtime-decision adequacy obligation.
-/
axiom ite_then_slot_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchSlotAdequacySupportCI Γ σ s
      (ite_then_profile_slot_payload_ci_of_entry hentry).branch

/--
Remaining else-branch slot-aware runtime-decision adequacy obligation.
-/
axiom ite_else_slot_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchSlotAdequacySupportCI Γ σ t
      (ite_else_profile_slot_payload_ci_of_entry hentry).branch

/-- Compatibility profile-level adequacy support for the then branch. -/
noncomputable def ite_then_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchAdequacySupportCI Γ σ s (ite_then_static_ci_of_entry hentry).profile := by
  simpa [ite_then_static_ci_of_entry, IteBranchStaticScaffoldCI.toBodyStaticBoundaryCI,
    IteBranchStaticScaffoldCI.profile, ite_then_static_scaffold_ci_of_entry,
    ite_then_profile_payload_ci_of_entry, IteBranchProfilePayloadCI.ofSlotPayload]
    using (ite_then_slot_adequacy_support_ci_of_entry hentry).toAdequacySupport

/-- Compatibility profile-level adequacy support for the else branch. -/
noncomputable def ite_else_adequacy_support_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchAdequacySupportCI Γ σ t (ite_else_static_ci_of_entry hentry).profile := by
  simpa [ite_else_static_ci_of_entry, IteBranchStaticScaffoldCI.toBodyStaticBoundaryCI,
    IteBranchStaticScaffoldCI.profile, ite_else_static_scaffold_ci_of_entry,
    ite_else_profile_payload_ci_of_entry, IteBranchProfilePayloadCI.ofSlotPayload]
    using (ite_else_slot_adequacy_support_ci_of_entry hentry).toAdequacySupport

/-- Compatibility adequacy wrapper for the then branch. -/
noncomputable def ite_then_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ s (ite_then_static_ci_of_entry hentry).profile :=
  (ite_then_adequacy_support_ci_of_entry hentry).toBodyAdequacyCI

/-- Compatibility adequacy wrapper for the else branch. -/
noncomputable def ite_else_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    BodyAdequacyCI Γ σ t (ite_else_static_ci_of_entry hentry).profile :=
  (ite_else_adequacy_support_ci_of_entry hentry).toBodyAdequacyCI

/--
Static+adequacy package for one branch of an `ite`.

Compatibility package assembled from the separated static scaffold and adequacy
obligations.  It is no longer a primitive axiom.
-/
structure IteBranchStaticAdequacyCI
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  static : BodyStaticBoundaryCI Γ st
  adequacy : BodyAdequacyCI Γ σ st static.profile

/-- Compatibility package for the then branch. -/
noncomputable def ite_then_static_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticAdequacyCI Γ σ s :=
  { static := ite_then_static_ci_of_entry hentry
    adequacy := ite_then_adequacy_ci_of_entry hentry }

/-- Compatibility package for the else branch. -/
noncomputable def ite_else_static_adequacy_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchStaticAdequacyCI Γ σ t :=
  { static := ite_else_static_ci_of_entry hentry
    adequacy := ite_else_adequacy_ci_of_entry hentry }

/--
Branch closure boundaries for an `ite`.

Compatibility package assembled from theorem-backed structural/dynamic
projections and the remaining static+adequacy branch obligations.
-/
structure IteBranchClosureBoundariesCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) : Type where
  thenBoundary : BodyClosureBoundaryCI Γ σ s
  elseBoundary : BodyClosureBoundaryCI Γ σ t

/--
Compatibility constructor for old callers.

The real remaining obligations are now the two static+adequacy branch packages;
the structural and dynamic pieces are theorem-backed.
-/
noncomputable def ite_branch_closure_boundaries_ci_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    IteBranchClosureBoundariesCI hentry := by
  let hthen := ite_then_static_adequacy_ci_of_entry hentry
  let helse := ite_else_static_adequacy_ci_of_entry hentry
  exact
    { thenBoundary :=
        mkBodyClosureBoundaryCI
          (ite_then_structural_boundary_of_entry hentry)
          hthen.static
          (ite_then_dynamic_boundary_of_entry hentry)
          hthen.adequacy
      elseBoundary :=
        mkBodyClosureBoundaryCI
          (ite_else_structural_boundary_of_entry hentry)
          helse.static
          (ite_else_dynamic_boundary_of_entry hentry)
          helse.adequacy }

/-- Extract condition readiness from a concrete-ready `ite`. -/
theorem ite_condition_ready_of_entry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t)) :
    ExprReadyConcrete Γ σ c (.base .bool) := by
  cases hentry.dynamic.safe with
  | ite _ hcond _ _ =>
      exact hcond

/-- Operational result assembly for the true branch of an `ite`. -/
theorem ite_function_body_result_true
    {σ : State} {c : ValExpr} {s t : CppStmt}
    (hcond : BigStepValue σ c (.bool true))
    (hthen : FunctionBodyClosureResult σ s) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  rcases hthen with hthenTerm | hthenDiv
  · rcases hthenTerm with ⟨ex, σ', hbody⟩
    cases hbody with
    | fallthrough hstep =>
        exact Or.inl ⟨.fellThrough, σ', BigStepFunctionBody.fallthrough
          (BigStepStmt.iteTrue hcond hstep)⟩
    | returning hstep =>
        rename_i rv
        exact Or.inl ⟨.returned rv, σ', BigStepFunctionBody.returning
          (BigStepStmt.iteTrue hcond hstep)⟩
  · exact Or.inr (BigStepStmtDiv.iteTrue hcond hthenDiv)

/-- Operational result assembly for the false branch of an `ite`. -/
theorem ite_function_body_result_false
    {σ : State} {c : ValExpr} {s t : CppStmt}
    (hcond : BigStepValue σ c (.bool false))
    (helse : FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  rcases helse with helseTerm | helseDiv
  · rcases helseTerm with ⟨ex, σ', hbody⟩
    cases hbody with
    | fallthrough hstep =>
        exact Or.inl ⟨.fellThrough, σ', BigStepFunctionBody.fallthrough
          (BigStepStmt.iteFalse hcond hstep)⟩
    | returning hstep =>
        rename_i rv
        exact Or.inl ⟨.returned rv, σ', BigStepFunctionBody.returning
          (BigStepStmt.iteFalse hcond hstep)⟩
  · exact Or.inr (BigStepStmtDiv.iteFalse hcond helseDiv)

/--
Theorem-backed `ite` closure shell.

The only abstract input is branch-boundary extraction. Once the condition is
ready, expression readiness supplies a boolean evaluation; the corresponding
branch closure is then lifted to the whole conditional by the operational
assembly lemmas above.
-/
theorem ite_function_body_closure_boundary_ci_honest
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.ite c s t))
    (thenClosure :
      BodyClosureBoundaryCI Γ σ s →
      FunctionBodyClosureResult σ s)
    (elseClosure :
      BodyClosureBoundaryCI Γ σ t →
      FunctionBodyClosureResult σ t) :
    FunctionBodyClosureResult σ (.ite c s t) := by
  let hb := ite_branch_closure_boundaries_ci_of_entry hentry
  have hcondReady : ExprReadyConcrete Γ σ c (.base .bool) :=
    ite_condition_ready_of_entry hentry
  rcases expr_ready_to_bigstep hcondReady with ⟨v, hcondEval⟩
  have hcompat : ValueCompat v (.base .bool) :=
    expr_ready_eval_compat hcondReady hcondEval
  cases hcompat with
  | bool =>
      rename_i b
      cases b with
      | false =>
          exact ite_function_body_result_false hcondEval
            (elseClosure hb.elseBoundary)
      | true =>
          exact ite_function_body_result_true hcondEval
            (thenClosure hb.thenBoundary)

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
