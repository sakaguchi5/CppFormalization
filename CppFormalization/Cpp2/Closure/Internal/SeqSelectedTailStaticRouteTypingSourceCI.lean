import CppFormalization.Cpp2.Closure.Internal.SeqSelectedTailStaticRouteTypingFromSelectionsCI

namespace Cpp

/-!
# Closure.Internal.SeqSelectedTailStaticRouteTypingSourceCI

A source-level lower layer for selected-tail static route typing.

`SeqSelectedTailStaticRouteTypingFromSelectionsCI` made the selection alignment
explicit: a queried payload `hp` must be the normal payload selected by the
normal-slot selection `N`.

This file separates the remaining static fact into a small source object.  The
source says which tail channel supplies the static boundary at the selected
environment `hp.Θ`:

* a normal tail channel gives both `typed0` and a normal root theoremically;
* a return tail channel gives the return root, but still needs an ordinary
  `WellTypedFrom hp.Θ t` payload, because a return-channel CI proof alone is not
  generally enough to recover the old coarse `WellTypedFrom` package.

C++ reading: once the left side of `s; t` selects the post-environment `hp.Θ`,
`t` must be statically readable in that environment.  The source below records
which visible tail channel supplies that static readability.
-/

/-- Build a tail static boundary from a selected normal tail typing. -/
def seq_tail_static_boundary_ci_of_normal_tail_typing
    {Θ Δ : TypeEnv} {t : CppStmt}
    (htail : HasTypeStmtCI .normalK Θ t Δ) :
    BodyStaticBoundaryCI Θ t :=
  { typed0 := ⟨Δ, normalCI_to_old_stmt htail⟩
    profile :=
      { summary :=
          { normalOut := some ⟨Δ, htail⟩
            returnOut := none } }
    root := .normal ⟨Δ, htail⟩
    rootCoherent := BodyRootCoherent.normal rfl }

/--
Build a tail static boundary from a selected return tail typing plus the coarse
old `WellTypedFrom` payload.

The extra `typed0` is intentional.  A CI return-channel proof does not, by
itself, imply the old coarse statement typing in this development.
-/
def seq_tail_static_boundary_ci_of_return_tail_typing
    {Θ Δ : TypeEnv} {t : CppStmt}
    (typed0 : WellTypedFrom Θ t)
    (htail : HasTypeStmtCI .returnK Θ t Δ) :
    BodyStaticBoundaryCI Θ t :=
  { typed0 := typed0
    profile :=
      { summary :=
          { normalOut := none
            returnOut := some ⟨Δ, htail⟩ } }
    root := .returned ⟨Δ, htail⟩
    rootCoherent := BodyRootCoherent.returned rfl }

/--
A source for the selected tail static boundary at `hp.Θ`.

The normal case is fully theorem-backed from normal CI typing.  The return case
keeps the necessary coarse `WellTypedFrom` payload explicit.
-/
inductive SeqSelectedTailStaticSourceCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  | normal
      {Δ : TypeEnv}
      (htail : HasTypeStmtCI .normalK hp.Θ t Δ) :
      SeqSelectedTailStaticSourceCI hentry hp
  | returned
      {Δ : TypeEnv}
      (typed0 : WellTypedFrom hp.Θ t)
      (htail : HasTypeStmtCI .returnK hp.Θ t Δ) :
      SeqSelectedTailStaticSourceCI hentry hp

namespace SeqSelectedTailStaticSourceCI

/-- Convert a selected-tail static source into the actual static boundary. -/
def toStatic
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqSelectedTailStaticSourceCI hentry hp) :
    BodyStaticBoundaryCI hp.Θ t := by
  cases S with
  | normal htail =>
      exact seq_tail_static_boundary_ci_of_normal_tail_typing htail
  | returned typed0 htail =>
      exact seq_tail_static_boundary_ci_of_return_tail_typing typed0 htail

end SeqSelectedTailStaticSourceCI

/--
A selected-tail static source together with the proof that `hp` is the normal
payload selected by `N`.
-/
structure SeqSelectedTailStaticSourceAtSelectionCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  selected : SeqSelectedNormalPayloadAtSelectionCI hentry D N hp
  source : SeqSelectedTailStaticSourceCI hentry hp

namespace SeqSelectedTailStaticSourceAtSelectionCI

/-- The static boundary carried by a selected source. -/
def toStatic
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqSelectedTailStaticSourceAtSelectionCI hentry D N hp) :
    BodyStaticBoundaryCI hp.Θ t :=
  S.source.toStatic

end SeqSelectedTailStaticSourceAtSelectionCI

/--
Source coverage for aligned selections.

This is the source-level form of `SeqSelectedTailStaticFromAlignedSelectionCI`:
for every payload known to be selected by `N`, provide a static source for the
tail at that selected environment.
-/
structure SeqSelectedTailStaticSourceFromAlignedSelectionCI : Type where
  sourceFromSelected :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (D : SeqStaticDecompositionCI hentry)
      (N : SeqLeftNormalSlotSelectionCI hentry D)
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedNormalPayloadAtSelectionCI hentry D N hp →
      SeqSelectedTailStaticSourceCI hentry hp

/-- Forget source coverage to the previous aligned-selection static interface. -/
def seqSelectedTailStaticFromAlignedSelectionCI_of_sources
    (S : SeqSelectedTailStaticSourceFromAlignedSelectionCI) :
    SeqSelectedTailStaticFromAlignedSelectionCI :=
  { staticFromSelected := by
      intro Γ σ s t hentry D N hp hsel
      exact (S.sourceFromSelected hentry D N hp hsel).toStatic }

/--
Canonical selected-tail source coverage.

This is the canonical counterpart of
`SeqCanonicalSelectedNormalPayloadCoverageCI`, but it carries both the alignment
proof and the static source.  It can therefore build the lower static route
typing directly.
-/
structure SeqCanonicalSelectedTailStaticSourceCoverageCI : Type where
  source :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      let D := seq_static_decomposition_ci_of_entry hentry
      let N := seq_left_normal_slot_selection_ci_of_decomposition hentry D
      SeqSelectedTailStaticSourceAtSelectionCI hentry D N hp

/-- Canonical source coverage yields lower selected-tail static route typing. -/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_staticSources
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  { static := by
      intro Γ σ s t hentry hp
      exact (C.source hentry hp).toStatic }

/--
Canonical source coverage also yields the corrected aligned-selection interface.
-/
noncomputable def seqCanonicalSelectedNormalPayloadCoverageCI_of_staticSources
    (C : SeqCanonicalSelectedTailStaticSourceCoverageCI) :
    SeqCanonicalSelectedNormalPayloadCoverageCI :=
  { selected := by
      intro Γ σ s t hentry hp
      exact (C.source hentry hp).selected }

/--
Design note wrapper: the real remaining static-route debt is now source coverage,
not boundary construction.
-/
structure SeqSelectedTailStaticRouteTypingSourcePackageCI : Type where
  coverage : SeqCanonicalSelectedTailStaticSourceCoverageCI

namespace SeqSelectedTailStaticRouteTypingSourcePackageCI

/-- Extract lower static route typing from the source package. -/
noncomputable def toRouteTyping
    (S : SeqSelectedTailStaticRouteTypingSourcePackageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  seqSelectedTailStaticRouteTypingCI_of_staticSources S.coverage

end SeqSelectedTailStaticRouteTypingSourcePackageCI

end Cpp
