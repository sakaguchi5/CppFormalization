import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
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

end Cpp
