import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseSplitCI

namespace Cpp

/-!
# Closure.Internal.SecondarySeqAssetsCI

Secondary assets for the sequence constructor case.

This file does not remove existing axioms directly.  It adds coherent
intermediate packages that make the later axiom replacement targets honest:
normal-slot selection and return-slot selection must be chosen together,
because tail-return provenance depends on the selected left-normal slot.

The witness-provider migration adds witness-producing adapters for the already
route-aware sequence adequacy packages.  These adapters make the future
`BodyAdequacyCI` provider replacement non-disruptive: the sequence case can
already produce `BodyAdequacyCI` where downstream Type-level data is
needed.
-/

/--
A coherent pair of left-side sequence slot selections.

`SeqLeftReturnSlotSelectionCI` is intentionally indexed by the selected
normal-slot package.  Bundling the two prevents downstream code from asking for
return-slot decisions for an arbitrary, incompatible normal selection.
-/
structure SeqLeftSlotSelectionBundleCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry) : Type where
  normal :
    SeqLeftNormalSlotSelectionCI hentry D
  returned :
    SeqLeftReturnSlotSelectionCI hentry D normal

namespace SeqLeftSlotSelectionBundleCI

/-- The selected normal slot of the bundled left profile. -/
def normalSlot
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (B : SeqLeftSlotSelectionBundleCI hentry D) :
    Option (SeqLeftNormalSlotCI Γ s) :=
  B.normal.normalSlot

/-- The selected return slot of the bundled left profile. -/
def returnSlot
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (B : SeqLeftSlotSelectionBundleCI hentry D) :
    Option (SeqLeftReturnSlotCI Γ s) :=
  B.returned.returnSlot

end SeqLeftSlotSelectionBundleCI

namespace SeqLeftProfileSlotPayloadCI

/--
Build the old slot-payload surface from a coherent normal/return bundle.

This is definition-only glue.  The important point is that the return component
is indexed by the bundled normal selection, so the tail-return case carries the
matching left-normal slot rather than merely proving that some normal slot
exists.
-/
def ofBundle
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (B : SeqLeftSlotSelectionBundleCI hentry D) :
    SeqLeftProfileSlotPayloadCI hentry D :=
  { normalSlot := B.normal.normalSlot
    returnSlot := B.returned.returnSlot
    normalFromWhole := by
      intro out hout
      exact B.normal.normalFromWhole hout
    returnFromWhole := by
      intro out hout
      exact B.returned.returnFromWhole hout }

/--
The profile induced by a coherent slot-selection bundle.
-/
def profileOfBundle
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (B : SeqLeftSlotSelectionBundleCI hentry D) :
    BodyControlProfile Γ s :=
  (ofBundle B).toProfile

/--
The Type-level support induced by a coherent slot-selection bundle.
-/
def supportOfBundle
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (B : SeqLeftSlotSelectionBundleCI hentry D) :
    SeqLeftProfileSupportCI hentry D (profileOfBundle B) :=
  (ofBundle B).toSupport

end SeqLeftProfileSlotPayloadCI

/--
Assemble the left static scaffold from a coherent slot-selection bundle.

This deliberately reuses the existing theorem-backed root/coherence constructor
`seq_left_root_scaffold_ci_of_profile`, so this file does not introduce any new
semantic assumption.
-/
noncomputable def seq_left_static_scaffold_ci_of_slotBundle
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (B : SeqLeftSlotSelectionBundleCI hentry D) :
    SeqLeftStaticScaffoldCI Γ s := by
  let P : BodyControlProfile Γ s :=
    SeqLeftProfileSlotPayloadCI.profileOfBundle B
  let S : SeqLeftProfileSupportCI hentry D P :=
    SeqLeftProfileSlotPayloadCI.supportOfBundle B
  let R : SeqLeftRootScaffoldCI Γ s P :=
    seq_left_root_scaffold_ci_of_profile hentry D P S
  exact
    { profile := P
      root := R.root
      rootCoherent := R.rootCoherent }

/--
Assemble the full left `BodyStaticBoundaryCI` from a coherent bundle and the
whole sequence entry.

The `typed0` component is already theorem-backed by `seq_left_typed0_of_entry`.
-/
noncomputable def seq_left_static_boundary_ci_of_slotBundle
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (B : SeqLeftSlotSelectionBundleCI hentry D) :
    BodyStaticBoundaryCI Γ s :=
  (seq_left_static_scaffold_ci_of_slotBundle hentry D B).toBodyStaticBoundaryCI
    (seq_left_typed0_of_entry hentry)

/--
A selected head-normal route for sequence tail entry.

This is not yet a tail-adequacy proof.  It is the small route object later
axioms should depend on instead of accepting an arbitrary left static package.
-/
structure SeqHeadNormalSelectedRouteCI
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    (B : SeqLeftSlotSelectionBundleCI hentry D)
    (hstep : BigStepStmt σ s .normal σ1) : Type where
  Θ : TypeEnv
  hleft : HasTypeStmtCI .normalK Γ s Θ
  selected : B.normal.normalSlot = some ⟨Θ, hleft⟩

namespace SeqHeadNormalSelectedRouteCI

/-- The profile-level normal payload induced by a selected head-normal route. -/
def toNormalPayload
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {B : SeqLeftSlotSelectionBundleCI hentry D}
    {hstep : BigStepStmt σ s .normal σ1}
    (R : SeqHeadNormalSelectedRouteCI B hstep) :
    SeqLeftNormalPayloadCI
      (SeqLeftProfileSlotPayloadCI.profileOfBundle B) :=
  { Θ := R.Θ
    hleft := R.hleft
    hprofile := by
      simp [SeqLeftProfileSlotPayloadCI.profileOfBundle,
        SeqLeftProfileSlotPayloadCI.ofBundle,
        SeqLeftProfileSlotPayloadCI.toProfile,
        R.selected, SeqLeftNormalSlotCI.out] }

end SeqHeadNormalSelectedRouteCI

/--
Witness-producing tail static+adequacy payload.

The existing `SeqTailStaticAdequacyPayloadCI` remains proof-only through
`SeqTailAdequacySupportCI`.  This payload exposes the same tail boundary as a
`BodyAdequacyCI`, which is the shape needed by the provider migration.
-/
structure SeqTailStaticAdequacyWitnessPayloadCI
    (Θ : TypeEnv) (σ1 : State) (t : CppStmt) : Type where
  static : BodyStaticBoundaryCI Θ t
  adequacyWitness : BodyAdequacyCI Θ σ1 t static.profile

namespace SeqTailStaticAdequacyWitnessPayloadCI

/-- Forget the witness-producing tail payload to the existing proof-only payload. -/
def toStaticAdequacyPayloadCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    (p : SeqTailStaticAdequacyWitnessPayloadCI Θ σ1 t) :
    SeqTailStaticAdequacyPayloadCI Θ σ1 t :=
  { static := p.static
    support :=
      { normal :=
          { normalSound := by
              intro σ2 hstep
              let w := p.adequacyWitness.normalWitness hstep
              exact ⟨w.val, w.property⟩ }
        returned :=
          { returnSound := by
              intro rv σ2 hstep
              let w := p.adequacyWitness.returnWitness hstep
              exact ⟨w.val, w.property⟩ } } }

/-- Forget the witness-producing tail payload to the older static+adequacy API. -/
noncomputable def toStaticAdequacyCI
    {Θ : TypeEnv} {σ1 : State} {t : CppStmt}
    (p : SeqTailStaticAdequacyWitnessPayloadCI Θ σ1 t) :
    SeqTailStaticAdequacyCI Θ σ1 t :=
  (p.toStaticAdequacyPayloadCI).toStaticAdequacyCI

end SeqTailStaticAdequacyWitnessPayloadCI

/--
Witness-producing compatibility name for the extracted left sequence boundary.
-/
noncomputable def seq_left_adequacy_witness_ci_of_entry
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    BodyAdequacyCI Γ σ s hstatic.profile :=
  (seq_left_adequacy_support_ci_of_entry hentry hstatic).toBodyAdequacyCI

end Cpp
