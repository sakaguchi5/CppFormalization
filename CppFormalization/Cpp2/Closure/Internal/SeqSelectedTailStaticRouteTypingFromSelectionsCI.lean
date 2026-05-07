import CppFormalization.Cpp2.Closure.Internal.SeqSelectedTailStaticRouteTypingCI

namespace Cpp

/-!
# Closure.Internal.SeqSelectedTailStaticRouteTypingFromSelectionsCI_corrected

Corrected lower static-route coverage interface.

The earlier selections interface passed a `SeqLeftNormalSlotSelectionCI` value `N`
but did not require the queried payload `hp` to be the payload selected by
`N.normalSlot`.  That made `N` semantically unused.

This file makes the missing alignment explicit.
-/

/--
`hp` is the left-normal payload selected by the normal-slot selection `N`.

This is a Type-level wrapper around the slot equality so downstream structures
+can depend on it while still returning Type-valued certificates.
-/
structure SeqSelectedNormalPayloadAtSelectionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  hslot : N.normalSlot = some ⟨hp.Θ, hp.hleft⟩

/-- Convenience constructor from the raw selected-slot equality. -/
def seqSelectedNormalPayloadAtSelectionCI_of_slot_eq
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (hslot : N.normalSlot = some ⟨hp.Θ, hp.hleft⟩) :
    SeqSelectedNormalPayloadAtSelectionCI hentry D N hp :=
  { hslot := hslot }

/--
Static typing for a payload that is known to be selected by the normal-slot
selection layer.

Here `N` is not decorative: the alignment proof says that the payload being
queried is exactly the selected normal slot of `N`.
-/
structure SeqSelectedTailStaticFromAlignedSelectionCI : Type where
  staticFromSelected :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (D : SeqStaticDecompositionCI hentry)
      (N : SeqLeftNormalSlotSelectionCI hentry D)
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedNormalPayloadAtSelectionCI hentry D N hp →
      BodyStaticBoundaryCI hp.Θ t

/--
Coverage for the canonical normal-slot selection used by the lower static route
layer.

This is the missing bridge from an arbitrary selected left-normal payload in the
left profile to the canonical selected normal slot.  Keeping it separate makes
clear that this is a static-route selection/alignment fact, not a closure or
runtime fact.
-/
structure SeqCanonicalSelectedNormalPayloadCoverageCI : Type where
  selected :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      let D := seq_static_decomposition_ci_of_entry hentry
      let N := seq_left_normal_slot_selection_ci_of_decomposition hentry D
      SeqSelectedNormalPayloadAtSelectionCI hentry D N hp

/--
Aligned selection support yields the lower static-route typing object.

Unlike the earlier interface, the use of `N` is real: we first obtain coverage
showing that `hp` is selected by the canonical `N`, then use the aligned static
support.
-/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_alignedSelections
    (C : SeqCanonicalSelectedNormalPayloadCoverageCI)
    (S : SeqSelectedTailStaticFromAlignedSelectionCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  { static := by
      intro Γ σ s t hentry hp
      let D := seq_static_decomposition_ci_of_entry hentry
      let N := seq_left_normal_slot_selection_ci_of_decomposition hentry D
      exact S.staticFromSelected hentry D N hp (C.selected hentry hp) }

/--
Local version for a fixed sequence entry and selected normal-slot layer.
-/
structure SeqSelectedTailStaticRouteTypingAtAlignedSelectionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D) : Type where
  staticAtSelected :
    ∀ (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedNormalPayloadAtSelectionCI hentry D N hp →
      BodyStaticBoundaryCI hp.Θ t

/-- Forget a family of local aligned-selection certificates to the global form. -/
def seqSelectedTailStaticFromAlignedSelectionCI_of_atAlignedSelection
    (S :
      ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
        (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
        (D : SeqStaticDecompositionCI hentry)
        (N : SeqLeftNormalSlotSelectionCI hentry D),
        SeqSelectedTailStaticRouteTypingAtAlignedSelectionCI hentry D N) :
    SeqSelectedTailStaticFromAlignedSelectionCI :=
  { staticFromSelected := by
      intro Γ σ s t hentry D N hp hsel
      exact (S hentry D N).staticAtSelected hp hsel }

end Cpp
