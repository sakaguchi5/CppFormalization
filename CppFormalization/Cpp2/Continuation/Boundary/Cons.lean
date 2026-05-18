import CppFormalization.Cpp2.Continuation.Boundary.Dynamic
import CppFormalization.Cpp2.Contracts.Obligations.ReadinessTransportNormalExactTail

namespace Cpp

/-!
# CppFormalization.Cpp2.Continuation.Boundary.Cons

Continuation boundary for the normal route of a nonempty block `s :: ss`.

The final design should obtain this from a selected head-normal route,
preservation, tail static boundary, stability/replay obligations, and adequacy
alignment.

For the current repository stage, this module provides a compatibility
constructor from the legacy exact-tail obligation.  Callers should depend on the
continuation boundary, not on the legacy transport statement.
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

/-- Legacy constructor for the current transition period.

This is intentionally the only place in the cons continuation surface where the
exact-tail obligation is used.
-/
theorem cons_normal_continuation_dynamic_of_exact_tail
    {Γ Θ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock}
    (hhead : HasTypeStmtCI .normalK Γ s Θ)
    (hpost : ScopedTypedStateConcrete Θ σ₁)
    (hreadyCons : BlockReadyConcrete Γ σ (.cons s ss))
    (hstepHead : BigStepStmt σ s .normal σ₁) :
    ConsNormalContinuationDynamicCI Γ Θ σ σ₁ s ss := by
  exact
    { hhead := hhead
      hstepHead := hstepHead
      tail :=
        { state := hpost
          safe :=
            cons_block_ready_tail_after_head_normal_of_exact_tail
              hhead hpost hreadyCons hstepHead } }

end Cpp
