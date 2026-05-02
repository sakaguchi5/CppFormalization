import CppFormalization.Cpp2.Closure.Internal.BlockBodyClosureConcreteCI
import CppFormalization.Cpp2.Closure.Internal.HeadTailReturnAwareRoutesCI
import CppFormalization.Cpp2.Closure.Foundation.BodyClosureBoundaryCI
import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Foundation.BodyAdequacyCI
import CppFormalization.Cpp2.Semantics.Divergence

namespace Cpp

/-!
# Closure.Internal.BlockBodyClosureAtCI

Current-environment block-body closure boundary.

This file introduces a current-environment block-body closure boundary and a
return-aware cons route that closes the head through a boundary/IH provider
rather than through the concrete master axiom.

The current organization is intentionally debt-transparent:
- head structural data is theorem-backed from cons block structural data;
- head typed0 is theorem-backed from the explicit cons normal payload;
- head profile/root/coherence are separated as a static scaffold;
- head adequacy is separated from head static;
- tail ready/profile/root are theorem-backed after a normal head step;
- tail adequacy is the remaining tail-side obligation.
-/

/-- Current-environment dynamic boundary for an opened block body. -/
structure BlockBodyDynamicBoundaryAtCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  state : ScopedTypedStateConcrete Γ σ
  safe : BlockReadyConcrete Γ σ ss

/-- Current-environment block-body adequacy. -/
structure BlockBodyAdequacyAtCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock)
    (P : BlockBodyControlProfileAt Γ ss) : Type where
  normalSound :
    ∀ {σ' : State} (_hstep : BigStepBlock σ ss .normal σ'),
      ∃ out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ ss Δ},
        P.summary.normalOut = some out
  returnSound :
    ∀ {rv : Option Value} {σ' : State}
      (_hstep : BigStepBlock σ ss (.returnResult rv) σ'),
      ∃ out : {Δ : TypeEnv // HasTypeBlockCI .returnK Γ ss Δ},
        P.summary.returnOut = some out

/-- Current-environment block-body static boundary. -/
structure BlockBodyStaticBoundaryAtCI
    (Γ : TypeEnv) (ss : StmtBlock) : Type where
  profile : BlockBodyControlProfileAt Γ ss
  root : BlockBodyEntryWitnessAt Γ ss
  rootCoherent : BlockBodyRootCoherentAt profile root

/-- Full current-environment block-body closure boundary. -/
structure BlockBodyClosureBoundaryAtCI
    (Γ : TypeEnv) (σ : State) (ss : StmtBlock) : Type where
  wf : WellFormedBlock ss
  breakScoped : BreakWellScopedBlockAt 0 ss
  continueScoped : ContinueWellScopedBlockAt 0 ss
  static : BlockBodyStaticBoundaryAtCI Γ ss
  dynamic : BlockBodyDynamicBoundaryAtCI Γ σ ss
  adequacy : BlockBodyAdequacyAtCI Γ σ ss static.profile

/-- Forget the closure boundary to the existing current-env readiness contract. -/
def BlockBodyClosureBoundaryAtCI.toReady
    {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
    (h : BlockBodyClosureBoundaryAtCI Γ σ ss) :
    BlockBodyReadyConcreteAtCI Γ σ ss :=
  { wf := h.wf
    profile := h.static.profile
    root := h.static.root
    rootCoherent := h.static.rootCoherent
    breakScoped := h.breakScoped
    continueScoped := h.continueScoped
    state := h.dynamic.state
    safe := h.dynamic.safe }

/--
Scaffold for extracting a head statement closure boundary from a current-env cons
block-body closure boundary.
-/
structure BlockConsHeadClosureScaffoldAtCI
    (Γ : TypeEnv) (σ : State) (s : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ s
  static : BodyStaticBoundaryCI Γ s
  adequacy : BodyAdequacyCI Γ σ s static.profile

/--
Head static scaffold without `typed0`.

`typed0` is no longer part of the scaffold: in the normal-channel cons route it
is theorem-backed from the explicit normal payload for the whole cons block.
The remaining static debt is profile/root/root-coherence.
-/
structure BlockConsHeadStaticScaffoldAtCI
    (Γ : TypeEnv) (s : CppStmt) : Type where
  profile : BodyControlProfile Γ s
  root : BodyEntryWitness Γ s
  rootCoherent : BodyRootCoherent profile root

/--
Head `typed0` from the explicit normal typing payload of a cons block.

For a normal typing of `.cons s ss`, the head statement necessarily has a normal
CI typing, and normal CI typing forgets to ordinary old typing.
-/
theorem blockCons_head_typed0_at_ci_of_normalOut
    {Γ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ}) :
    WellTypedFrom Γ s := by
  rcases out with ⟨Δ, htyBlock⟩
  cases htyBlock with
  | cons_normal htyHead htyTail =>
      exact ⟨_, normalCI_to_old_stmt htyHead⟩

/--
Head static scaffold extraction.

This is the remaining static-side obligation after removing `typed0` from the
axiom.  It may depend on the chosen normal cons payload, because that is the
actual route used to close the head in this normal-channel theorem.
-/
axiom blockCons_head_static_scaffold_at_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hout : hentry.static.profile.summary.normalOut = some out) :
    BlockConsHeadStaticScaffoldAtCI Γ s

/-- Assemble a `BodyStaticBoundaryCI` from theorem-backed `typed0` plus scaffold. -/
def BlockConsHeadStaticScaffoldAtCI.toBodyStaticBoundaryCI
    {Γ : TypeEnv} {s : CppStmt} {ss : StmtBlock}
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (h : BlockConsHeadStaticScaffoldAtCI Γ s) :
    BodyStaticBoundaryCI Γ s :=
  { typed0 := blockCons_head_typed0_at_ci_of_normalOut out
    profile := h.profile
    root := h.root
    rootCoherent := h.rootCoherent }

/-- Head static extraction assembled from theorem-backed `typed0` and scaffold. -/
noncomputable def blockCons_head_static_boundary_at_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hout : hentry.static.profile.summary.normalOut = some out) :
    BodyStaticBoundaryCI Γ s :=
  let hsc := blockCons_head_static_scaffold_at_ci_of_boundary hentry out hout
  hsc.toBodyStaticBoundaryCI out

/--
Head adequacy extraction for a given extracted head static boundary.

This is kept separate from head static extraction because adequacy is semantic
evidence.  Conflating the two would hide the real proof obligation.
-/
axiom blockCons_head_adequacy_at_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (hstatic : BodyStaticBoundaryCI Γ s) :
    BodyAdequacyCI Γ σ s hstatic.profile

/-- The head statement inherits structural well-formedness/scoping from cons. -/
theorem blockCons_head_structural_boundary_at_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss)) :
    BodyStructuralBoundary Γ s := by
  have hwf : WellFormedStmt s ∧ WellFormedBlock ss := by
    simpa [WellFormedBlock] using hentry.wf
  have hbreak : BreakWellScoped s ∧ BreakWellScopedBlockAt 0 ss := by
    simpa [BreakWellScopedBlockAt] using hentry.breakScoped
  have hcont : ContinueWellScoped s ∧ ContinueWellScopedBlockAt 0 ss := by
    simpa [ContinueWellScopedBlockAt] using hentry.continueScoped
  exact
    { wf := hwf.1
      breakScoped := hbreak.1
      continueScoped := hcont.1 }

/--
Extract the head closure scaffold from a cons block-body closure boundary.

This is now assembled from:
- theorem-backed structural data;
- theorem-backed `typed0` plus head static scaffold;
- head adequacy extraction.
-/
noncomputable def blockCons_head_closure_scaffold_at_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hout : hentry.static.profile.summary.normalOut = some out) :
    BlockConsHeadClosureScaffoldAtCI Γ σ s :=
  let hstatic := blockCons_head_static_boundary_at_ci_of_boundary hentry out hout
  { structural := blockCons_head_structural_boundary_at_ci_of_boundary hentry
    static := hstatic
    adequacy := blockCons_head_adequacy_at_ci_of_boundary hentry hstatic }

/-- Dynamic head boundary for the head statement of a cons block body. -/
def blockCons_head_dynamic_boundary_at_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss)) :
    BodyDynamicBoundary Γ σ s :=
  { state := hentry.dynamic.state
    safe := cons_block_ready_head hentry.dynamic.safe }

/-- Full head statement boundary extracted from a cons block-body boundary. -/
noncomputable def blockCons_head_closure_boundary_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hout : hentry.static.profile.summary.normalOut = some out) :
    BodyClosureBoundaryCI Γ σ s := by
  let hs := blockCons_head_closure_scaffold_at_ci_of_boundary hentry out hout
  let hd := blockCons_head_dynamic_boundary_at_ci_of_boundary hentry
  exact mkBodyClosureBoundaryCI hs.structural hs.static hd hs.adequacy

/--
Tail adequacy after an actual normal head execution.

The tail ready/profile/root package is theorem-backed by
`blockBodyReadyConcreteAtCI_cons_tail_after_head_normal`; the remaining
non-trivial piece is the adequacy package for that tail boundary.
-/
axiom blockCons_tail_adequacy_at_ci_of_head_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hstep : BigStepStmt σ s .normal σ')
    {Θ : TypeEnv}
    (htailReady : BlockBodyReadyConcreteAtCI Θ σ' ss) :
    BlockBodyAdequacyAtCI Θ σ' ss htailReady.profile

/--
Tail closure boundary after an actual normal head execution.

This is theorem-backed up to the named tail-adequacy obligation above.
-/
theorem blockCons_tail_closure_boundary_at_ci_of_head_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hstep : BigStepStmt σ s .normal σ') :
    ∃ Θ, ∃ htail : BlockBodyClosureBoundaryAtCI Θ σ' ss,
      ∃ outTail, htail.static.profile.summary.normalOut = some outTail := by
  rcases blockBodyReadyConcreteAtCI_cons_tail_after_head_normal
      mkWhileReentry hentry.toReady out hstep with
    ⟨Θ, htailReady, htailN⟩
  let htail : BlockBodyClosureBoundaryAtCI Θ σ' ss :=
    { wf := htailReady.wf
      breakScoped := htailReady.breakScoped
      continueScoped := htailReady.continueScoped
      static :=
        { profile := htailReady.profile
          root := htailReady.root
          rootCoherent := htailReady.rootCoherent }
      dynamic :=
        { state := htailReady.state
          safe := htailReady.safe }
      adequacy :=
        blockCons_tail_adequacy_at_ci_of_head_normal
          mkWhileReentry hentry out hstep htailReady }
  exact ⟨Θ, htail, htailN⟩

/--
Decomposed cons-boundary certificate.

This is the real object the cons route needs:
- a closure scaffold for the head statement for the selected normal route;
- a tail closure boundary provider for the actual head-normal execution.
-/
structure BlockConsClosureDecompositionAtCI
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss)) : Type where
  head :
    ∀ (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ}),
      hentry.static.profile.summary.normalOut = some out →
      BlockConsHeadClosureScaffoldAtCI Γ σ s
  tailAfterHeadNormal :
    ∀ {σ' : State}
      (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ}),
      hentry.static.profile.summary.normalOut = some out →
      BigStepStmt σ s .normal σ' →
      ∃ Θ, ∃ htail : BlockBodyClosureBoundaryAtCI Θ σ' ss,
        ∃ outTail, htail.static.profile.summary.normalOut = some outTail

/-- Compatibility constructor for the decomposed cons-boundary certificate. -/
noncomputable def blockConsClosureDecompositionAtCI_of_scaffolds
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss)) :
    BlockConsClosureDecompositionAtCI hentry :=
  { head := by
      intro out hout
      exact blockCons_head_closure_scaffold_at_ci_of_boundary hentry out hout
    tailAfterHeadNormal := by
      intro σ' out _hout hstep
      exact blockCons_tail_closure_boundary_at_ci_of_head_normal
        mkWhileReentry hentry out hstep }

/-- Full head statement boundary extracted from a cons decomposition certificate. -/
noncomputable def blockCons_head_closure_boundary_ci_of_decomposition
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (D : BlockConsClosureDecompositionAtCI hentry)
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hout : hentry.static.profile.summary.normalOut = some out) :
    BodyClosureBoundaryCI Γ σ s := by
  let hs := D.head out hout
  let hd := blockCons_head_dynamic_boundary_at_ci_of_boundary hentry
  exact mkBodyClosureBoundaryCI hs.structural hs.static hd hs.adequacy

/--
Cons block-body closure from an explicit decomposition certificate.
-/
theorem block_cons_function_body_closure_boundary_at_ci_with_decomposition
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (D : BlockConsClosureDecompositionAtCI hentry)
    (hN : ∃ out, hentry.static.profile.summary.normalOut = some out)
    (headClosure :
      BodyClosureBoundaryCI Γ σ s →
        (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s)
    (tailClosure :
      ∀ {Θ : TypeEnv} {σ' : State}
        (htail : BlockBodyClosureBoundaryAtCI Θ σ' ss),
        (∃ out, htail.static.profile.summary.normalOut = some out) →
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons s ss) ex σ') ∨
      BigStepBlockDiv σ (.cons s ss) := by
  rcases hN with ⟨out, hout⟩
  have hheadBoundary : BodyClosureBoundaryCI Γ σ s :=
    blockCons_head_closure_boundary_ci_of_decomposition hentry D out hout
  have hhead :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s :=
    headClosure hheadBoundary
  exact
    block_cons_function_body_result_return_aware
      hhead
      (fun hstep =>
        match D.tailAfterHeadNormal out hout hstep with
        | ⟨Θ, htail, htailN⟩ =>
            tailClosure htail htailN)

/--
Current-env block-body closure through statement IH, parameterized by an explicit
cons-decomposition provider.
-/
theorem block_body_function_closure_boundary_at_ci_normalOut_with_decomposition
    (headClosure :
      ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
        BodyClosureBoundaryCI Γ σ st →
          (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st)
    (decomposeCons :
      ∀ {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
        (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss)),
        BlockConsClosureDecompositionAtCI hentry) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
      (hentry : BlockBodyClosureBoundaryAtCI Γ σ ss),
      (∃ out, hentry.static.profile.summary.normalOut = some out) →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨
        BigStepBlockDiv σ ss
  | _, _, .nil, _hentry, _hN =>
      Or.inl ⟨.fellThrough, _, BigStepFunctionBlockBody.fallthrough BigStepBlock.nil⟩
  | _, _, .cons _ _, hentry, hN =>
      block_cons_function_body_closure_boundary_at_ci_with_decomposition
        hentry
        (decomposeCons hentry)
        hN
        (fun hheadBoundary => headClosure hheadBoundary)
        (fun htail htailN =>
          block_body_function_closure_boundary_at_ci_normalOut_with_decomposition
            headClosure
            decomposeCons
            htail
            htailN)

/--
Cons block-body closure from a statement-boundary/IH head provider and a
recursive current-env block-body closure provider.

Compatibility wrapper.
-/
theorem block_cons_function_body_closure_boundary_at_ci_with_IH
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (hN : ∃ out, hentry.static.profile.summary.normalOut = some out)
    (headClosure :
      BodyClosureBoundaryCI Γ σ s →
        (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s)
    (tailClosure :
      ∀ {Θ : TypeEnv} {σ' : State}
        (htail : BlockBodyClosureBoundaryAtCI Θ σ' ss),
        (∃ out, htail.static.profile.summary.normalOut = some out) →
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨
          BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons s ss) ex σ') ∨
      BigStepBlockDiv σ (.cons s ss) := by
  exact
    block_cons_function_body_closure_boundary_at_ci_with_decomposition
      hentry
      (blockConsClosureDecompositionAtCI_of_scaffolds mkWhileReentry hentry)
      hN
      headClosure
      tailClosure

/--
Current-env block-body closure through statement IH.

Compatibility wrapper.
-/
theorem block_body_function_closure_boundary_at_ci_normalOut_with_IH
    (mkWhileReentry : WhileReentryReadyProvider)
    (headClosure :
      ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
        BodyClosureBoundaryCI Γ σ st →
          (∃ ex σ', BigStepFunctionBody σ st ex σ') ∨ BigStepStmtDiv σ st) :
    ∀ {Γ : TypeEnv} {σ : State} {ss : StmtBlock}
      (hentry : BlockBodyClosureBoundaryAtCI Γ σ ss),
      (∃ out, hentry.static.profile.summary.normalOut = some out) →
      (∃ ex σ', BigStepFunctionBlockBody σ ss ex σ') ∨
        BigStepBlockDiv σ ss :=
  block_body_function_closure_boundary_at_ci_normalOut_with_decomposition
    headClosure
    (fun hentry =>
      blockConsClosureDecompositionAtCI_of_scaffolds mkWhileReentry hentry)

end Cpp
