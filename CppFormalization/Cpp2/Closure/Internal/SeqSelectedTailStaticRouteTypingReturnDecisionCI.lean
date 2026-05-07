import CppFormalization.Cpp2.Closure.Internal.SeqSelectedTailStaticRouteTypingSourceCI

namespace Cpp

/-!
# Closure.Internal.SeqSelectedTailStaticRouteTypingReturnDecisionCI

A non-dependent-elimination version of the decision-source layer for selected-tail
static route typing.

The important design choice in this file is that the selected decision itself is
not used as an index of an inductive family.  Doing that forces Lean to prove
that a value such as `N.normalDecision hout` is definitionally equal to a
particular constructor branch, which is exactly the dependent-elimination problem
we want to avoid.

Instead, the source records the branch data that a normal decision or a
 tail-return decision provides:

* normal whole-sequence decision: selected normal slot + tail normal typing;
* tail-return decision: selected normal slot + tail return typing + coarse
  `WellTypedFrom` for the tail.

C++ reading: after `s` falls through in `s; t`, the tail `t` is statically read
at the selected post-environment.  A whole-sequence normal route supplies a
normal typing for `t`; a tail-originated return route supplies a return typing
for `t` and still needs the ordinary coarse typing payload for `t`.
-/

/--
A normal decision source for a selected left-normal payload.

This is the payload carried by a `SeqNormalSlotDecisionCI.normal` branch, but it
is represented as a record rather than as an indexed family over the decision
term.  That keeps downstream conversions free of dependent `cases`.
-/
structure SeqNormalDecisionSourceAtPayloadCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  out : {Δ : TypeEnv // HasTypeStmtCI .normalK Γ (.seq s t) Δ}
  hout : hentry.static.profile.summary.normalOut = some out
  Δ : TypeEnv
  htail : HasTypeStmtCI .normalK hp.Θ t Δ
  houtDef : out = ⟨Δ, HasTypeStmtCI.seq_normal hp.hleft htail⟩
  hslot : N.normalSlot = some ⟨hp.Θ, hp.hleft⟩

namespace SeqNormalDecisionSourceAtPayloadCI

/-- The selected-payload alignment carried by a normal decision source. -/
def selected
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqNormalDecisionSourceAtPayloadCI hentry D N hp) :
    SeqSelectedNormalPayloadAtSelectionCI hentry D N hp :=
  { hslot := S.hslot }

/-- Convert a normal decision source into the selected-tail static source API. -/
def toSourceAtSelection
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqNormalDecisionSourceAtPayloadCI hentry D N hp) :
    SeqSelectedTailStaticSourceAtSelectionCI hentry D N hp :=
  { selected := S.selected
    source := SeqSelectedTailStaticSourceCI.normal S.htail }

end SeqNormalDecisionSourceAtPayloadCI

/--
A tail-return decision source for a selected left-normal payload.

This is the payload carried by a `SeqReturnSlotDecisionCI.tailReturn` branch,
plus the coarse `typed0` needed to build a `BodyStaticBoundaryCI` for `t`.
Again, it is a record rather than an indexed family over `R.returnDecision hout`.
-/
structure SeqTailReturnDecisionSourceAtPayloadCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (R : SeqLeftReturnSlotSelectionCI hentry D N)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ (.seq s t) Δ}
  hout : hentry.static.profile.summary.returnOut = some out
  Δ : TypeEnv
  typed0 : WellTypedFrom hp.Θ t
  htail : HasTypeStmtCI .returnK hp.Θ t Δ
  houtDef : out = ⟨Δ, HasTypeStmtCI.seq_normal hp.hleft htail⟩
  hslot : N.normalSlot = some ⟨hp.Θ, hp.hleft⟩

namespace SeqTailReturnDecisionSourceAtPayloadCI

/-- The selected-payload alignment carried by a tail-return decision source. -/
def selected
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {R : SeqLeftReturnSlotSelectionCI hentry D N}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqTailReturnDecisionSourceAtPayloadCI hentry D N R hp) :
    SeqSelectedNormalPayloadAtSelectionCI hentry D N hp :=
  { hslot := S.hslot }

/-- Convert a tail-return decision source into the selected-tail static source API. -/
def toSourceAtSelection
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {R : SeqLeftReturnSlotSelectionCI hentry D N}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqTailReturnDecisionSourceAtPayloadCI hentry D N R hp) :
    SeqSelectedTailStaticSourceAtSelectionCI hentry D N hp :=
  { selected := S.selected
    source := SeqSelectedTailStaticSourceCI.returned S.typed0 S.htail }

end SeqTailReturnDecisionSourceAtPayloadCI

/--
A selected-tail static source justified either by a whole-sequence normal source
or by a tail-originated return source.
-/
inductive SeqSelectedTailStaticDecisionSourceCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (R : SeqLeftReturnSlotSelectionCI hentry D N)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  | normal
      (S : SeqNormalDecisionSourceAtPayloadCI hentry D N hp) :
      SeqSelectedTailStaticDecisionSourceCI hentry D N R hp
  | tailReturn
      (S : SeqTailReturnDecisionSourceAtPayloadCI hentry D N R hp) :
      SeqSelectedTailStaticDecisionSourceCI hentry D N R hp

namespace SeqSelectedTailStaticDecisionSourceCI

/-- Convert decision-source evidence to the existing source-at-selection API. -/
def toSourceAtSelection
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {R : SeqLeftReturnSlotSelectionCI hentry D N}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqSelectedTailStaticDecisionSourceCI hentry D N R hp) :
    SeqSelectedTailStaticSourceAtSelectionCI hentry D N hp := by
  cases S with
  | normal S => exact S.toSourceAtSelection
  | tailReturn S => exact S.toSourceAtSelection

end SeqSelectedTailStaticDecisionSourceCI

/--
Decision-source coverage for selected-tail static route typing.

For each selected normal payload, the static source must come either from a
whole-sequence normal source or from a tail-return source.  This remains purely
static: it contains no runtime state and no head-step argument.
-/
structure SeqSelectedTailStaticDecisionSourceCoverageCI : Type where
  source :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (D : SeqStaticDecompositionCI hentry)
      (N : SeqLeftNormalSlotSelectionCI hentry D)
      (R : SeqLeftReturnSlotSelectionCI hentry D N)
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedTailStaticDecisionSourceCI hentry D N R hp

/-- Decision-source coverage gives canonical selected-tail static source coverage. -/
noncomputable def seqCanonicalSelectedTailStaticSourceCoverageCI_of_decisionSources
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI) :
    SeqCanonicalSelectedTailStaticSourceCoverageCI :=
  { source := by
      intro Γ σ s t hentry hp
      let D := seq_static_decomposition_ci_of_entry hentry
      let N := seq_left_normal_slot_selection_ci_of_decomposition hentry D
      let R := seq_left_return_slot_selection_ci_of_decomposition hentry D N
      exact (C.source hentry D N R hp).toSourceAtSelection }

/-- Decision-source coverage yields lower static route typing. -/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_decisionSources
    (C : SeqSelectedTailStaticDecisionSourceCoverageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  seqSelectedTailStaticRouteTypingCI_of_staticSources
    (seqCanonicalSelectedTailStaticSourceCoverageCI_of_decisionSources C)

end Cpp
