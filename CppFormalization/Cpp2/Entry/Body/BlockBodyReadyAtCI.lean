import CppFormalization.Cpp2.Static.WellFormed
import CppFormalization.Cpp2.Static.ScopeDiscipline
import CppFormalization.Cpp2.Static.Typing.ControlIndexed
import CppFormalization.Cpp2.Entry.StaticSafety.Readiness
import CppFormalization.Cpp2.Validity.StateInvariantConcrete.StateInvariantConcrete
import CppFormalization.Cpp2.Operational.Stmt
import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Closure.Package.BodyClosureBoundaryCI

namespace Cpp

/-!
# Entry.Body.BlockBodyReadyAtCI

CI-native current-environment readiness surfaces.

This file is deliberately *not* phrased through old coarse typing:
there is no `HasTypeStmt`, no `HasTypeBlock`, and no `WellTypedFrom`.

The goal is to replace the concrete current-env opened block-body route

`BlockBodyReadyConcreteAt`

with an explicitly CI-indexed route that can be driven by
`CompoundContinuation`.
-/

/--
CI-native statement entry used by opened block-body head execution.

`normalTypingOfStep` is the local adequacy hook needed by the cons-normal case:
if the head statement actually exits normally, the selected normal typing payload
is available.
-/
structure BodyReadyAtCI (Γ : TypeEnv) (σ : State) (st : CppStmt) : Type where
  wf : WellFormedStmt st
  breakScoped : BreakWellScoped st
  continueScoped : ContinueWellScoped st
  state : ScopedTypedStateConcrete Γ σ
  safe : StmtReadyConcrete Γ σ st
  normalTypingOfStep :
    ∀ {σ' : State},
      BigStepStmt σ st .normal σ' →
      ∃ Δ : TypeEnv, HasTypeStmtCI .normalK Γ st Δ

namespace BodyReadyAtCI

/--
Build the CI-native statement entry from an assembled statement closure boundary.

This is theorem-backed by `BodyAdequacyCI.normalWitness`: a normal statement
execution selects a concrete normal CI typing payload from the profile.
-/
def ofClosureBoundary
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : BodyClosureBoundaryCI Γ σ st) :
    BodyReadyAtCI Γ σ st :=
  { wf := h.structural.wf
    breakScoped := h.structural.breakScoped
    continueScoped := h.structural.continueScoped
    state := h.dynamic.state
    safe := h.dynamic.safe
    normalTypingOfStep := by
      intro σ' hstep
      let w := h.adequacy.normalWitness hstep
      exact ⟨w.val.val, w.val.property⟩ }

end BodyReadyAtCI

/--
CI-native opened/current block-body entry.

`BlockBodyReadyAtCI` intentionally stores no old coarse block typing payload.
Tail rebuilding is externalized into providers below, so the structure itself is
not recursively defined and passes Lean's positivity checker.
-/
structure BlockBodyReadyAtCI (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  wf : WellFormedBlock ss
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss
  state : ScopedTypedStateConcrete Γ σ
  safe : BlockReadyConcrete Γ σ ss

  headReadyOfCons :
    ∀ {head : CppStmt} {tail : StmtBlock},
      ss = .cons head tail →
      BodyReadyAtCI Γ σ head

/--
Dynamic tail provider used by the CI-native opened block-body closure.

This should ultimately be built from
`CompoundContinuation.Cons.Tail.ContinuationInput.toDynamicBoundary`.
-/
abbrev BlockBodyReadyAtCITailDynamicProvider : Prop :=
  ∀ {Γ Θ : TypeEnv} {σ σ' : State} {head : CppStmt} {tail : StmtBlock},
    BlockBodyReadyAtCI Γ σ (.cons head tail) →
    HasTypeStmtCI .normalK Γ head Θ →
    BigStepStmt σ head .normal σ' →
    BlockContinuationDynamicBoundary Θ σ' tail

/--
Rebuild the CI-native tail entry once the dynamic continuation boundary is known.

This is separated from `BlockBodyReadyAtCI` itself to avoid recursive structure
fields.
-/
abbrev BlockBodyReadyAtCITailRebuildProvider : Type :=
  ∀ {Γ Θ : TypeEnv} {σ σ' : State} {head : CppStmt} {tail : StmtBlock},
    BlockBodyReadyAtCI Γ σ (.cons head tail) →
    HasTypeStmtCI .normalK Γ head Θ →
    BigStepStmt σ head .normal σ' →
    BlockContinuationDynamicBoundary Θ σ' tail →
    BlockBodyReadyAtCI Θ σ' tail

/--
Combined tail-after-head provider consumed by block-body closure.
-/
/-
Legacy physical definition for the block-cons normal successor provider.

New public code should prefer

  `ControlSuccessor.BlockConsNormalSuccessorProvider`

from `Continuation.Successor.BlockCons`.

This definition remains here to keep `Entry.Body` independent from the
`Continuation.Successor` vocabulary layer and avoid import reversal.
-/
abbrev BlockBodyReadyAtCITailAfterHeadProvider : Type :=
  ∀ {Γ Θ : TypeEnv} {σ σ' : State} {head : CppStmt} {tail : StmtBlock},
    BlockBodyReadyAtCI Γ σ (.cons head tail) →
    HasTypeStmtCI .normalK Γ head Θ →
    BigStepStmt σ head .normal σ' →
    BlockBodyReadyAtCI Θ σ' tail

namespace BlockBodyReadyAtCITailAfterHeadProvider

/-- Compose a dynamic tail provider and a tail-entry rebuild provider. -/
def ofDynamicAndRebuild
    (tailDynamic : BlockBodyReadyAtCITailDynamicProvider)
    (tailRebuild : BlockBodyReadyAtCITailRebuildProvider) :
    BlockBodyReadyAtCITailAfterHeadProvider := by
  intro Γ Θ σ σ' head tail h hty hstep
  exact tailRebuild h hty hstep (tailDynamic h hty hstep)

end BlockBodyReadyAtCITailAfterHeadProvider

/--
Head extraction provider for converting an assembled opened block-body boundary
into the CI-native current-env block-body entry.

This is the intentionally small replacement for the previous monolithic
`blockBodyReadyAtCI_of_blockBodyClosureBoundaryCI` axiom.
-/
abbrev BlockBodyReadyAtCIHeadProvider : Type :=
  ∀ {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock},
    BlockBodyClosureBoundaryCI Γ σ (.cons head tail) →
    BodyReadyAtCI (pushTypeScope Γ) σ head

/--
A lower provider that supplies an ordinary statement closure boundary for the
head of an opened block body.
-/
abbrev BlockBodyReadyAtCIHeadBoundaryProvider : Type :=
  ∀ {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock},
    BlockBodyClosureBoundaryCI Γ σ (.cons head tail) →
    BodyClosureBoundaryCI (pushTypeScope Γ) σ head

namespace BlockBodyReadyAtCIHeadProvider

/-- Build the head-ready provider from a statement closure-boundary provider. -/
def ofBodyClosureBoundaryProvider
    (mkHeadBoundary : BlockBodyReadyAtCIHeadBoundaryProvider) :
    BlockBodyReadyAtCIHeadProvider := by
  intro Γ σ head tail h
  exact BodyReadyAtCI.ofClosureBoundary (mkHeadBoundary h)

end BlockBodyReadyAtCIHeadProvider

/--
Decomposed conversion from assembled opened block-body boundary to the CI-native
current-env entry.

The old monolithic axiom is replaced by one explicit missing ingredient:
`headProvider`, which explains how to obtain the CI-native head statement entry
for the `cons` case.
-/
def blockBodyReadyAtCI_of_blockBodyClosureBoundaryCI_withHeadProvider
    (headProvider : BlockBodyReadyAtCIHeadProvider)
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyClosureBoundaryCI Γ σ ss) :
    BlockBodyReadyAtCI (pushTypeScope Γ) σ ss :=
  { wf := h.structural.wf
    breakScoped := h.structural.breakScoped
    continueScoped := h.structural.continueScoped
    state := h.dynamic.state
    safe := h.dynamic.safe
    headReadyOfCons := by
      intro head tail hEq
      cases hEq
      exact headProvider h }

end Cpp
