import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Contracts.Obligations.ReadinessTransportNormalExactTail

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.Seq

Continuation boundary for the normal route of `s; t`.

The final design should obtain this from a selected route, preservation,
tail-static boundary, stability/replay obligations, and adequacy alignment.

For the current repository stage, this module provides a compatibility
constructor from the legacy exact-tail obligation.  Callers should depend on the
continuation boundary, not on the legacy transport statement.
-/

/-- Dynamic continuation boundary after the left side of a sequence finishes
normally. -/
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

/-- Legacy constructor for the current transition period.

This is intentionally the only place in the seq continuation surface where the
exact-tail obligation is used.
-/
theorem seq_normal_continuation_dynamic_of_exact_tail
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (hleft : HasTypeStmtCI .normalK Γ s Θ)
    (hpost : ScopedTypedStateConcrete Θ σ₁)
    (hreadySeq : StmtReadyConcrete Γ σ (.seq s t))
    (hstepLeft : BigStepStmt σ s .normal σ₁) :
    SeqNormalContinuationDynamicCI Γ Θ σ σ₁ s t := by
  exact
    { hleft := hleft
      hstepLeft := hstepLeft
      tail :=
        { state := hpost
          safe :=
            seq_ready_right_after_left_normal_of_exact_tail
              hleft hpost hreadySeq hstepLeft } }


/- =========================================================
   Full continuation boundary surface
   ========================================================= -/

/-- Full continuation boundary after the left side of a sequence finishes
normally.

This is the intended public shape for selected-route seq continuation:
the route determines the post environment/state, and the tail is represented by
a full continuation boundary rather than by a readiness transport statement.
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

/-- Build the full seq continuation boundary from an existing tail closure
boundary.

This is a compatibility constructor: it lets route-aware callers switch their
callback surface from `BodyClosureBoundaryCI` to `SeqNormalContinuationBoundaryCI`
without changing the old closure assembly yet.
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

end Cpp
