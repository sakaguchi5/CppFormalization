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

`BlockBodyReadyConcreteAtCI` is enough for readiness and the concrete fallback
route, but it is not enough to feed an IH/CI head-closure provider: the head
statement needs a real `BodyClosureBoundaryCI`, including static profile and
adequacy.

This file introduces a current-environment block-body closure boundary and a
return-aware cons route that closes the head through a boundary/IH provider
rather than through the concrete master axiom.
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

This is the honest lower-level debt: a block-body closure boundary should carry
enough static/adequacy information to close its head statement through the
ordinary statement IH.
-/
structure BlockConsHeadClosureScaffoldAtCI
    (Γ : TypeEnv) (σ : State) (s : CppStmt) : Type where
  structural : BodyStructuralBoundary Γ s
  static : BodyStaticBoundaryCI Γ s
  adequacy : BodyAdequacyCI Γ σ s static.profile

/--
Extract the head closure scaffold from a cons block-body closure boundary.

This is intentionally a scaffold obligation, not hidden inside the cons closure
theorem.  It is the block analogue of the seq-left scaffold debt.
-/
axiom blockCons_head_closure_scaffold_at_ci_of_boundary
    {Γ : TypeEnv} {σ : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss)) :
    BlockConsHeadClosureScaffoldAtCI Γ σ s

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
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss)) :
    BodyClosureBoundaryCI Γ σ s := by
  let hs := blockCons_head_closure_scaffold_at_ci_of_boundary hentry
  let hd := blockCons_head_dynamic_boundary_at_ci_of_boundary hentry
  exact mkBodyClosureBoundaryCI hs.structural hs.static hd hs.adequacy

/--
Tail closure boundary after an actual normal head execution.

This is the second honest lower-level debt.  Dynamic readiness can be obtained
from preservation/readiness transport, but the full closure boundary also needs
a tail static profile and adequacy package.  Keeping this as a named obligation
is much better than routing through the concrete master axiom.
-/
axiom blockCons_tail_closure_boundary_at_ci_of_head_normal
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {s : CppStmt} {ss : StmtBlock}
    (hentry : BlockBodyClosureBoundaryAtCI Γ σ (.cons s ss))
    (out : {Δ : TypeEnv // HasTypeBlockCI .normalK Γ (.cons s ss) Δ})
    (hstep : BigStepStmt σ s .normal σ') :
    ∃ Θ, ∃ htail : BlockBodyClosureBoundaryAtCI Θ σ' ss,
      ∃ outTail, htail.static.profile.summary.normalOut = some outTail

/--
Cons block-body closure from a statement-boundary/IH head provider and a
recursive current-env block-body closure provider.

This is the route that actually makes the head closure provider usable:
the head is closed via `BodyClosureBoundaryCI`, not via `BodyReadyConcrete`.
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
        (∃ ex σ'', BigStepFunctionBlockBody σ' ss ex σ'') ∨ BigStepBlockDiv σ' ss) :
    (∃ ex σ', BigStepFunctionBlockBody σ (.cons s ss) ex σ') ∨
      BigStepBlockDiv σ (.cons s ss) := by
  rcases hN with ⟨out, _hout⟩
  have hheadBoundary : BodyClosureBoundaryCI Γ σ s :=
    blockCons_head_closure_boundary_ci_of_boundary hentry
  have hhead :
      (∃ ex σ', BigStepFunctionBody σ s ex σ') ∨ BigStepStmtDiv σ s :=
    headClosure hheadBoundary
  exact
    block_cons_function_body_result_return_aware
      hhead
      (fun hstep =>
        match blockCons_tail_closure_boundary_at_ci_of_head_normal
            mkWhileReentry hentry out hstep with
        | ⟨Θ, htail, htailN⟩ =>
            tailClosure htail htailN)

/--
Current-env block-body closure through statement IH.

This is the recursive boundary-level counterpart of
`block_body_function_closure_concrete_refined_at_ci_with_headClosure`.
It avoids committing to the concrete master for head statements.
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
        BigStepBlockDiv σ ss
  | _, _, .nil, _hentry, _hN =>
      Or.inl ⟨.fellThrough, _, BigStepFunctionBlockBody.fallthrough BigStepBlock.nil⟩
  | _, _, .cons _ _, hentry, hN =>
      block_cons_function_body_closure_boundary_at_ci_with_IH
        mkWhileReentry
        hentry
        hN
        (fun hheadBoundary => headClosure hheadBoundary)
        (fun htail htailN =>
          block_body_function_closure_boundary_at_ci_normalOut_with_IH
            mkWhileReentry
            headClosure
            htail
            htailN)

end Cpp
