import CppFormalization.Cpp2.Closure.Internal.SeqTailReturnTyped0SupportCI

namespace Cpp

/-!
# Closure.Internal.SeqTailCoarseTypingAtSelectedNormalCI

A lower static layer for the coarse tail typedness used by tail-return selected
routes.

`SeqTailReturnTyped0SupportCI` says that once the selected normal payload of the
left side of `s; t` chooses a post-environment `hp.Θ`, the tail `t` is ordinarily
well typed from that environment.

That fact is not a return-decision fact.  It is the coarse typing component of
sequence route typing.  This file isolates that component as its own lower static
source and shows how it discharges the `typed0` support used by the tail-return
source layer.
-/

/--
A coarse old-style typing source for the tail at a selected normal payload.

C++ reading: after the selected normal completion of `s` in `s; t`, the tail
`t` is statically readable from the selected post-environment `hp.Θ`.

This is deliberately independent of the return-slot selection `R`: whether `t`
is well typed from `hp.Θ` is a static route fact, not a fact about which return
channel was selected.
-/
structure SeqTailCoarseTypingAtSelectedNormalCI : Type where
  tailTyped :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (D : SeqStaticDecompositionCI hentry)
      (N : SeqLeftNormalSlotSelectionCI hentry D)
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedNormalPayloadAtSelectionCI hentry D N hp →
      WellTypedFrom hp.Θ t

/--
The coarse selected-tail typing source discharges the tail-return `typed0`
support.
-/
def seqTailReturnTyped0SupportCI_of_tailCoarseTyping
    (C : SeqTailCoarseTypingAtSelectedNormalCI) :
    SeqTailReturnTyped0SupportCI :=
  { typed0 := by
      intro Γ σ s t hentry D N hp hsel
      exact C.tailTyped hentry D N hp hsel }

/--
A direct old typing witness for the selected tail.

This wrapper is sometimes easier to provide than `WellTypedFrom`, while still
remaining fully static and lower-level.
-/
structure SeqTailOldTypingSourceAtSelectedNormalCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  selected : SeqSelectedNormalPayloadAtSelectionCI hentry D N hp
  Δ : TypeEnv
  htail : HasTypeStmt hp.Θ t Δ

namespace SeqTailOldTypingSourceAtSelectedNormalCI

/-- Convert an old typing source into the `WellTypedFrom` payload. -/
def toWellTypedFrom
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqTailOldTypingSourceAtSelectedNormalCI hentry D N hp) :
    WellTypedFrom hp.Θ t :=
  ⟨S.Δ, S.htail⟩

end SeqTailOldTypingSourceAtSelectedNormalCI

/--
Coverage by old typing sources for every selected normal payload.
-/
structure SeqTailOldTypingSourceCoverageCI : Type where
  source :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (D : SeqStaticDecompositionCI hentry)
      (N : SeqLeftNormalSlotSelectionCI hentry D)
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedNormalPayloadAtSelectionCI hentry D N hp →
      SeqTailOldTypingSourceAtSelectedNormalCI hentry D N hp

/--
Old typing source coverage yields the coarse selected-tail typing support.
-/
def seqTailCoarseTypingAtSelectedNormalCI_of_oldTypingSources
    (C : SeqTailOldTypingSourceCoverageCI) :
    SeqTailCoarseTypingAtSelectedNormalCI :=
  { tailTyped := by
      intro Γ σ s t hentry D N hp hsel
      exact (C.source hentry D N hp hsel).toWellTypedFrom }

/--
A normal CI tail typing source also gives old coarse typing for the selected tail.

This is the theorem-backed part: normal CI typing forgets to old normal typing.
-/
def seqTailOldTypingSourceAtSelectedNormalCI_of_normalDecisionSource
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqNormalDecisionSourceAtPayloadCI hentry D N hp) :
    SeqTailOldTypingSourceAtSelectedNormalCI hentry D N hp :=
  { selected := S.selected
    Δ := S.Δ
    htail := normalCI_to_old_stmt S.htail }

/--
Split decision-source coverage plus selected-tail coarse typing yields lower
selected-tail static route typing.

This is the same construction as the previous `typed0` layer, but with the
`typed0` support produced from a lower coarse-typing source.
-/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_returnTypingAndTailCoarseTyping
    (T : SeqTailCoarseTypingAtSelectedNormalCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  seqSelectedTailStaticRouteTypingCI_of_returnTypingAndTyped0DecisionSources
    (seqTailReturnTyped0SupportCI_of_tailCoarseTyping T)
    C

/--
Variant using old typing source coverage directly.
-/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_returnTypingAndOldTypingSources
    (T : SeqTailOldTypingSourceCoverageCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  seqSelectedTailStaticRouteTypingCI_of_returnTypingAndTailCoarseTyping
    (seqTailCoarseTypingAtSelectedNormalCI_of_oldTypingSources T)
    C

end Cpp
