import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Continuation.Compound.Cons.Tail.Continuation

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.Cons

Continuation boundary for the normal route of a nonempty block `s :: ss`.

The public subject is continuation boundary, not readiness transport.  The old
exact-tail readiness transport path is no longer imported here: callers that
want to cross from the head normal step to the block tail must provide an
explicit post-route tail continuation, preferably through `CompoundContinuation`.
-/

/-- Dynamic continuation boundary after the head of a block finishes normally. -/
structure ConsNormalContinuationDynamicCI
    (Γ Θ : TypeEnv) (σ σ₁ : State) (s : CppStmt) (ss : StmtBlock) : Prop where
  hhead : HasTypeStmtCI .normalK Γ s Θ
  hstepHead : BigStepStmt σ s .normal σ₁
  tail : BlockContinuationDynamicBoundary Θ σ₁ ss

theorem ConsNormalContinuationDynamicCI.postState
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock}
    (h : ConsNormalContinuationDynamicCI Γ Θ σ σ₁ s ss) :
    ScopedTypedStateConcrete Θ σ₁ :=
  h.tail.state

theorem ConsNormalContinuationDynamicCI.tailReady
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock}
    (h : ConsNormalContinuationDynamicCI Γ Θ σ σ₁ s ss) :
    BlockReadyConcrete Θ σ₁ ss :=
  h.tail.safe

/--
Build the dynamic cons-continuation compatibility surface from an explicit block
tail dynamic boundary.

This is the small replacement for the old exact-tail constructor: the proof of
post-route block-tail readiness is no longer hidden inside a transport axiom, but
is carried by `tail`.
-/
def cons_normal_continuation_dynamic_of_tail_dynamic_boundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock}
    (hhead : HasTypeStmtCI .normalK Γ s Θ)
    (hstepHead : BigStepStmt σ s .normal σ₁)
    (tail : BlockContinuationDynamicBoundary Θ σ₁ ss) :
    ConsNormalContinuationDynamicCI Γ Θ σ σ₁ s ss :=
  { hhead := hhead
    hstepHead := hstepHead
    tail := tail }


/- =========================================================
   CompoundContinuation selected-route bridge
   ========================================================= -/

/--
Build the dynamic cons-continuation compatibility surface from the new
`CompoundContinuation` cons tail continuation input.

The route core is indexed by the tail environment `Θ`, because the continuation
target is the block tail after the head has finished normally.
-/
def cons_normal_continuation_dynamic_of_compound_continuation
    {Γ Θ : TypeEnv} {σ σ1 : State} {s : CppStmt} {ss : StmtBlock}
    (hhead : HasTypeStmtCI .normalK Γ s Θ)
    (route : CompoundContinuation.Cons.HeadNormalRouteCore Θ σ σ1 s ss)
    (input : CompoundContinuation.Cons.Tail.ContinuationInput route) :
    ConsNormalContinuationDynamicCI Γ Θ σ σ1 s ss :=
  { hhead := hhead
    hstepHead := route.hhead
    tail := input.toDynamicBoundary }

end Cpp
