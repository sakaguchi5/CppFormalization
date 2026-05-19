import CppFormalization.Cpp2.Contracts.Obligations.ReadinessTransportNormalExactTail
import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay
import CppFormalization.Cpp2.Continuation.Boundary.Body
import CppFormalization.Cpp2.Boundary.Static.SeqStaticBoundaryProjectionCI

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.Seq

Seq continuation boundary assembly.

This file has two roles during the transition:

1. Keep the legacy exact-tail compatibility surface:
   `SeqNormalContinuationDynamicCI`
   `seq_normal_continuation_dynamic_of_exact_tail`
   `SeqNormalContinuationBoundaryCI`

2. Provide the newer selected-route continuation assembly:
   `seq_tail_continuation_boundary_ci_of_head_normal_route`

The public subject should be continuation boundary, not readiness transport.
The exact-tail constructor is retained only for old callers.
-/

/- =========================================================
   Legacy seq normal-continuation compatibility surface
   ========================================================= -/

/--
Dynamic continuation boundary after the left side of a sequence finishes
normally.

This is the old public compatibility surface used by sequential normal
preservation and while compatibility handlers.
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
Legacy constructor for the current transition period.

This is intentionally the exact-tail compatibility constructor needed by old
sequential-preservation surfaces.  New route-aware code should prefer selected
route + stability/replay + continuation boundary assembly.
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
   Legacy full continuation boundary surface
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

Compatibility constructor for callers that already have an ordinary tail
closure boundary.
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
   Selected-route continuation boundary assembly
   ========================================================= -/

/--
Build the full post-state tail continuation from the selected route plus the
route-local stability contract.

Static and adequacy come from the selected route.
Dynamic readiness comes from the explicit route-local stability/replay contract.
-/
noncomputable def seq_tail_continuation_boundary_ci_of_head_normal_route
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P)
    (stability : SeqTailStabilityAtRouteCI route) :
    StmtContinuationBoundaryCI route.Θ σ1 t :=
  { structural := seq_tail_structural_boundary_of_entry hentry
    static := route.tail.static
    dynamic := stability.toStmtContinuationDynamicBoundary
    adequacy := route.tail.support.toBodyAdequacyCI }

end Cpp
