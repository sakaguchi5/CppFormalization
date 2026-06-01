import CppFormalization.Cpp2.Profile.StaticBoundary.SeqStaticBoundaryProjectionCI
import CppFormalization.Cpp2.Static.SeqStatic.SeqTypingProvenanceCI
import CppFormalization.Cpp2.Closure.Package.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Static.SeqStatic.SeqStructuralProjectionCI

namespace Cpp

/-!
# Seq boundary/static decomposition compatibility layer

This module contains the current `BodyClosureBoundaryCI`-indexed sequence
static/profile decomposition API.

It was split out of the mistakenly placed
`Static/Pure/SeqStaticDecompositionCI.lean`.  The facts here are useful, but
they are not pure static facts because their public carrier is a closure
boundary.
-/

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

/-- Compatibility wrapper from the current full closure boundary carrier. -/
theorem seq_left_typed0_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    WellTypedFrom Γ s :=
  seq_left_typed0_of_static hentry.static

/-- Compatibility wrapper from the current full closure boundary carrier. -/
theorem seq_left_structural_boundary_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStructuralBoundary Γ s :=
  seq_left_structural_boundary_of_structural hentry.structural

/-- Compatibility wrapper from the current full closure boundary carrier. -/
theorem seq_tail_structural_boundary_of_entry
    {Γ Θ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) :
    BodyStructuralBoundary Θ t :=
  seq_tail_structural_boundary_of_structural hentry.structural

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
Type-level static decomposition data for the left side of a sequence.

`SeqStaticDecompositionCI` remains a `Prop`: it says the whole sequence profile
has seq-shaped provenance.  This structure is the separate Type-level data:
it chooses a normal slot and the matching return-slot dispatcher together.

This avoids the bad direction

`SeqStaticDecompositionCI : Prop` → `SeqLeftNormalSlotSelectionCI : Type`

in the mainline.  Compatibility declarations may still expose the older
projection names, but the mainline should consume this bundle.
-/
structure SeqLeftSlotSelectionDataCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) : Type where
  decomposition : SeqStaticDecompositionCI hentry
  normal : SeqLeftNormalSlotSelectionCI hentry decomposition
  returned : SeqLeftReturnSlotSelectionCI hentry decomposition normal

namespace SeqLeftSlotSelectionDataCI

/-- The old slot-payload surface induced by Type-level slot-selection data. -/
def toProfileSlots
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    (D : SeqLeftSlotSelectionDataCI hentry) :
    SeqLeftProfileSlotPayloadCI hentry D.decomposition :=
  SeqLeftProfileSlotPayloadCI.ofSelections D.normal D.returned

/-- The left profile payload induced by Type-level slot-selection data. -/
def toProfilePayload
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    (D : SeqLeftSlotSelectionDataCI hentry) :
    SeqLeftProfilePayloadCI hentry D.decomposition :=
  let S := D.toProfileSlots
  { profile := S.toProfile
    support := S.toSupport }

end SeqLeftSlotSelectionDataCI


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
Assemble the full left static scaffold from Type-level slot-selection data.
-/
noncomputable def SeqLeftSlotSelectionDataCI.staticScaffoldPayload
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    (D : SeqLeftSlotSelectionDataCI hentry) :
    { S : SeqLeftStaticScaffoldCI Γ s //
      SeqLeftStaticScaffoldCompatibleCI hentry D.decomposition S } := by
  let Ppack := D.toProfilePayload
  let R :=
    seq_left_root_scaffold_ci_of_profile
      hentry
      D.decomposition
      Ppack.profile
      Ppack.support
  refine
    ⟨{ profile := Ppack.profile
       root := R.root
       rootCoherent := R.rootCoherent }, ?_⟩
  exact
    { profileCompatible := Ppack.support.toCompatible }

/-- Static scaffold projected from Type-level slot-selection data. -/
noncomputable def SeqLeftSlotSelectionDataCI.staticScaffold
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    (D : SeqLeftSlotSelectionDataCI hentry) :
    SeqLeftStaticScaffoldCI Γ s :=
  (D.staticScaffoldPayload).1

/-- Compatibility certificate for the data-backed static scaffold. -/
theorem SeqLeftSlotSelectionDataCI.staticScaffoldCompatible
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    (D : SeqLeftSlotSelectionDataCI hentry) :
    SeqLeftStaticScaffoldCompatibleCI hentry D.decomposition D.staticScaffold :=
  (D.staticScaffoldPayload).2

/-- Left static boundary assembled from Type-level slot-selection data. -/
noncomputable def SeqLeftSlotSelectionDataCI.staticBoundary
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    (D : SeqLeftSlotSelectionDataCI hentry) :
    BodyStaticBoundaryCI Γ s :=
  D.staticScaffold.toBodyStaticBoundaryCI
    (seq_left_typed0_of_static hentry.static)

end Cpp
