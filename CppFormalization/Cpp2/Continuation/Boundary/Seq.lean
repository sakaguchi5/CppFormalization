import CppFormalization.Cpp2.Continuation.Compound.Seq.Tail.Continuation
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Profile.StaticBoundary.SeqStaticBoundaryProjectionCI
import CppFormalization.Cpp2.Static.SeqStatic.SeqStructuralProjectionCI

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.Seq

Seq continuation boundary assembly.

The public subject is continuation boundary, not readiness transport.  The old
exact-tail readiness transport path is no longer imported here: callers that
want to cross from the left normal step to the tail must provide an explicit
post-route tail continuation, preferably through `CompoundContinuation`.
-/

/- =========================================================
   Seq normal-continuation compatibility surface
   ========================================================= -/

/--
Dynamic continuation boundary after the left side of a sequence finishes
normally.

This compatibility surface is still useful for older downstream code, but it is
now fed by explicit tail continuation evidence rather than by the legacy
exact-tail readiness transport axiom.
-/
structure SeqNormalContinuationDynamicCI
    (Γ Θ : TypeEnv) (σ σ₁ : State) (s t : CppStmt) : Prop where
  hleft : HasTypeStmtCI .normalK Γ s Θ
  hstepLeft : BigStepStmt σ s .normal σ₁
  tail : StmtContinuationDynamicBoundary Θ σ₁ t

theorem SeqNormalContinuationDynamicCI.postState
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationDynamicCI Γ Θ σ σ₁ s t) :
    ScopedTypedStateConcrete Θ σ₁ :=
  h.tail.state

theorem SeqNormalContinuationDynamicCI.tailReady
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationDynamicCI Γ Θ σ σ₁ s t) :
    StmtReadyConcrete Θ σ₁ t :=
  h.tail.safe

def SeqNormalContinuationDynamicCI.toBodyDynamicBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationDynamicCI Γ Θ σ σ₁ s t) :
    BodyDynamicBoundary Θ σ₁ t :=
  h.tail.toBodyDynamicBoundary

/--
Build the dynamic seq-continuation compatibility surface from an explicit tail
dynamic boundary.

This is the small replacement for the old exact-tail constructor: the proof of
post-route tail readiness is no longer hidden inside a transport axiom, but is
carried by `tail`.
-/
def seq_normal_continuation_dynamic_of_tail_dynamic_boundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (hleft : HasTypeStmtCI .normalK Γ s Θ)
    (hstepLeft : BigStepStmt σ s .normal σ₁)
    (tail : StmtContinuationDynamicBoundary Θ σ₁ t) :
    SeqNormalContinuationDynamicCI Γ Θ σ σ₁ s t :=
  { hleft := hleft
    hstepLeft := hstepLeft
    tail := tail }

/- =========================================================
   Full continuation boundary surface
   ========================================================= -/

/--
Full continuation boundary after the left side of a sequence finishes normally.

This is a compatibility wrapper over `StmtContinuationBoundaryCI`.
-/
structure SeqNormalContinuationBoundaryCI
    (Γ Θ : TypeEnv) (σ σ₁ : State) (s t : CppStmt) : Type where
  hleft : HasTypeStmtCI .normalK Γ s Θ
  hstepLeft : BigStepStmt σ s .normal σ₁
  tail : StmtContinuationBoundaryCI Θ σ₁ t

namespace SeqNormalContinuationBoundaryCI

def dynamic
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationBoundaryCI Γ Θ σ σ₁ s t) :
    SeqNormalContinuationDynamicCI Γ Θ σ σ₁ s t :=
  { hleft := h.hleft
    hstepLeft := h.hstepLeft
    tail := h.tail.dynamic }

def tailBodyClosureBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationBoundaryCI Γ Θ σ σ₁ s t) :
    BodyClosureBoundaryCI Θ σ₁ t :=
  h.tail.toBodyClosureBoundaryCI

def tailBodyReady
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationBoundaryCI Γ Θ σ σ₁ s t) :
    BodyReadyCI Θ σ₁ t :=
  h.tail.toBodyReadyCI

theorem tailReady
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationBoundaryCI Γ Θ σ σ₁ s t) :
    StmtReadyConcrete Θ σ₁ t :=
  h.tail.ready

theorem postState
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (h : SeqNormalContinuationBoundaryCI Γ Θ σ σ₁ s t) :
    ScopedTypedStateConcrete Θ σ₁ :=
  h.tail.postState

end SeqNormalContinuationBoundaryCI

/--
Build the full seq continuation boundary from an existing tail closure boundary.

Compatibility constructor for callers that already have an ordinary tail closure
boundary.
-/
def seq_normal_continuation_boundary_of_tail_closure_boundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (hleft : HasTypeStmtCI .normalK Γ s Θ)
    (hstepLeft : BigStepStmt σ s .normal σ₁)
    (tail : BodyClosureBoundaryCI Θ σ₁ t) :
    SeqNormalContinuationBoundaryCI Γ Θ σ σ₁ s t :=
  { hleft := hleft
    hstepLeft := hstepLeft
    tail := StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI tail }



/- =========================================================
   CompoundContinuation selected-route bridge
   ========================================================= -/

/--
Build the dynamic seq-continuation compatibility surface from the new
`CompoundContinuation` route-local continuation input.

The dynamic tail readiness is materialized from

* post-state preservation, and
* componentized route-local tail replay

inside `CompoundContinuation.Seq.Tail.ContinuationInput`.
-/
def seq_normal_continuation_dynamic_of_compound_continuation
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (input : CompoundContinuation.Seq.Tail.ContinuationInput route.toCore) :
    SeqNormalContinuationDynamicCI Γ route.Θ σ σ1 s t :=
  { hleft := route.hleft
    hstepLeft := route.hstepLeft
    tail := by
      simpa [SeqHeadNormalRouteCI.toCore] using input.toDynamicBoundary }

/--
Build the full seq tail continuation boundary from the selected route plus the
new `CompoundContinuation` continuation input.

This is the selected-route replacement target for the old exact-tail path:
static and adequacy come from `route.tail`; dynamic readiness comes from
CompoundContinuation replay.
-/
noncomputable def seq_tail_continuation_boundary_ci_of_compound_continuation
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (input : CompoundContinuation.Seq.Tail.ContinuationInput route.toCore) :
    StmtContinuationBoundaryCI route.Θ σ1 t :=
  { structural := seq_tail_structural_boundary_of_structural hentry.structural
    static := route.tail.static
    dynamic := by
      simpa [SeqHeadNormalRouteCI.toCore] using input.toDynamicBoundary
    adequacy := route.tail.support.toBodyAdequacyCI }

end Cpp
