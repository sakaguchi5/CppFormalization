import CppFormalization.Cpp2.Closure.Internal.SeqSelectedTailStaticRouteTypingReturnDecisionCI

namespace Cpp

/-!
# Closure.Internal.SeqTailReturnTyped0SupportCI

Separates the coarse tail typedness needed by the tail-return selected-route
source.

At the previous layer, a tail-return source carried

* selected normal-slot alignment;
* a tail return CI typing;
* `typed0 : WellTypedFrom hp.Θ t`.

The last field is not a runtime or adequacy fact.  It is a lower static typing
fact: once the selected normal payload chooses the post-environment `hp.Θ`, the
tail `t` is ordinarily well typed from that environment.

This file factors that `typed0` field out of the tail-return source.
-/

/--
Coarse typedness for the tail at a selected normal payload.

C++ reading: in `s; t`, after the selected normal exit of `s` chooses the
post-environment `hp.Θ`, the tail `t` is statically readable from `hp.Θ`.

This is deliberately separate from the tail-return CI typing.  A return-channel
CI proof records a control path; the ordinary `WellTypedFrom` payload records
that the tail statement itself is well typed from the selected environment.
-/
structure SeqTailReturnTyped0SupportCI : Type where
  typed0 :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (D : SeqStaticDecompositionCI hentry)
      (N : SeqLeftNormalSlotSelectionCI hentry D)
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedNormalPayloadAtSelectionCI hentry D N hp →
      WellTypedFrom hp.Θ t

/--
Tail-return decision source without the coarse `typed0`.

This is the part that really comes from the tail-return branch:

* a visible whole-sequence return channel;
* a tail return CI typing from the selected environment;
* equality showing the whole return channel is `seq_normal hp.hleft htail`;
* equality showing the selected normal slot is exactly `hp`.

The missing `WellTypedFrom hp.Θ t` is supplied separately by
`SeqTailReturnTyped0SupportCI`.
-/
structure SeqTailReturnDecisionReturnTypingSourceCI
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
  htail : HasTypeStmtCI .returnK hp.Θ t Δ
  houtDef : out = ⟨Δ, HasTypeStmtCI.seq_normal hp.hleft htail⟩
  hslot : N.normalSlot = some ⟨hp.Θ, hp.hleft⟩

namespace SeqTailReturnDecisionReturnTypingSourceCI

/-- The selected-payload alignment carried by the tail-return typing source. -/
def selected
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {R : SeqLeftReturnSlotSelectionCI hentry D N}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqTailReturnDecisionReturnTypingSourceCI hentry D N R hp) :
    SeqSelectedNormalPayloadAtSelectionCI hentry D N hp :=
  { hslot := S.hslot }

/--
Reassemble the previous tail-return source by supplying the separated
`typed0` support.
-/
def toSourceAtPayload
    (T0 : SeqTailReturnTyped0SupportCI)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {R : SeqLeftReturnSlotSelectionCI hentry D N}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqTailReturnDecisionReturnTypingSourceCI hentry D N R hp) :
    SeqTailReturnDecisionSourceAtPayloadCI hentry D N R hp :=
  { out := S.out
    hout := S.hout
    Δ := S.Δ
    typed0 := T0.typed0 hentry D N hp S.selected
    htail := S.htail
    houtDef := S.houtDef
    hslot := S.hslot }

end SeqTailReturnDecisionReturnTypingSourceCI

/--
Convenience top-level constructor.

This is just `SeqTailReturnDecisionReturnTypingSourceCI.toSourceAtPayload` with a
more searchable name.
-/
def seqTailReturnDecisionSourceAtPayloadCI_of_returnTypingAndTyped0
    (T0 : SeqTailReturnTyped0SupportCI)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {R : SeqLeftReturnSlotSelectionCI hentry D N}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqTailReturnDecisionReturnTypingSourceCI hentry D N R hp) :
    SeqTailReturnDecisionSourceAtPayloadCI hentry D N R hp :=
  S.toSourceAtPayload T0

/--
Decision-source evidence where the tail-return branch carries only the return
typing, while the coarse `typed0` is factored out globally.

The normal branch is unchanged: normal CI typing already supplies enough static
information for the tail static boundary.
-/
inductive SeqSelectedTailStaticDecisionReturnTypingSourceCI
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (D : SeqStaticDecompositionCI hentry)
    (N : SeqLeftNormalSlotSelectionCI hentry D)
    (R : SeqLeftReturnSlotSelectionCI hentry D N)
    (hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile) : Type where
  | normal
      (S : SeqNormalDecisionSourceAtPayloadCI hentry D N hp) :
      SeqSelectedTailStaticDecisionReturnTypingSourceCI hentry D N R hp
  | tailReturn
      (S : SeqTailReturnDecisionReturnTypingSourceCI hentry D N R hp) :
      SeqSelectedTailStaticDecisionReturnTypingSourceCI hentry D N R hp

namespace SeqSelectedTailStaticDecisionReturnTypingSourceCI

/--
Reassemble the previous decision-source evidence by supplying the separated
tail-return `typed0` support.
-/
def toDecisionSource
    (T0 : SeqTailReturnTyped0SupportCI)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.seq s t)}
    {D : SeqStaticDecompositionCI hentry}
    {N : SeqLeftNormalSlotSelectionCI hentry D}
    {R : SeqLeftReturnSlotSelectionCI hentry D N}
    {hp : SeqLeftNormalPayloadCI
      (seq_left_static_boundary_ci_of_entry hentry).profile}
    (S : SeqSelectedTailStaticDecisionReturnTypingSourceCI hentry D N R hp) :
    SeqSelectedTailStaticDecisionSourceCI hentry D N R hp := by
  cases S with
  | normal S =>
      exact SeqSelectedTailStaticDecisionSourceCI.normal S
  | tailReturn S =>
      exact SeqSelectedTailStaticDecisionSourceCI.tailReturn
        (S.toSourceAtPayload T0)

end SeqSelectedTailStaticDecisionReturnTypingSourceCI

/--
Coverage using the split tail-return source.

For every selected normal payload, we get either:

* a normal decision source; or
* a tail-return decision source without `typed0`.

The separated `SeqTailReturnTyped0SupportCI` supplies the missing coarse
typedness only for the tail-return branch.
-/
structure SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI : Type where
  source :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt}
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
      (D : SeqStaticDecompositionCI hentry)
      (N : SeqLeftNormalSlotSelectionCI hentry D)
      (R : SeqLeftReturnSlotSelectionCI hentry D N)
      (hp : SeqLeftNormalPayloadCI
        (seq_left_static_boundary_ci_of_entry hentry).profile),
      SeqSelectedTailStaticDecisionReturnTypingSourceCI hentry D N R hp

/--
Combine split decision-source coverage with tail-return `typed0` support to
recover the previous decision-source coverage.
-/
def seqSelectedTailStaticDecisionSourceCoverageCI_of_returnTypingAndTyped0
    (T0 : SeqTailReturnTyped0SupportCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqSelectedTailStaticDecisionSourceCoverageCI :=
  { source := by
      intro Γ σ s t hentry D N R hp
      exact (C.source hentry D N R hp).toDecisionSource T0 }

/--
Split decision-source coverage plus tail-return typedness support yields the
lower selected-tail static route typing object.
-/
noncomputable def seqSelectedTailStaticRouteTypingCI_of_returnTypingAndTyped0DecisionSources
    (T0 : SeqTailReturnTyped0SupportCI)
    (C : SeqSelectedTailStaticDecisionReturnTypingSourceCoverageCI) :
    SeqSelectedTailStaticRouteTypingCI :=
  seqSelectedTailStaticRouteTypingCI_of_decisionSources
    (seqSelectedTailStaticDecisionSourceCoverageCI_of_returnTypingAndTyped0 T0 C)

end Cpp
