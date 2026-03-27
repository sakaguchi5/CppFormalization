import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Closure.Internal.ReadinessBoundaryConcrete

namespace Cpp
namespace InternalClosureRoadmapConcrete

/-!
Concrete internal closure roadmap.

This file is intentionally thin: it does not introduce new proofs.
It freezes the concrete kernel/interface that is now theorem-backed,
so later closure layers can depend on a stable concrete contract
without pulling in the lower-level implementation details directly.
-/

-- Preservation kernel

theorem stmt_normal_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {s : CppStmt}
    (hty : HasTypeStmtCI .normalK Γ s Δ)
    (hready : StmtReadyConcrete Γ σ s)
    (hstep : BigStepStmt σ s .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ' :=
  Cpp.stmt_normal_preserves_scoped_typed_state_concrete hty hσ hready hstep

theorem block_body_normal_preserves_scoped_typed_state
    {Γ Δ : TypeEnv} {σ σ' : State} {ss : StmtBlock}
    (hty : HasTypeBlockCI .normalK Γ ss Δ)
    (hready : BlockReadyConcrete Γ σ ss)
    (hstep : BigStepBlock σ ss .normal σ')
    (hσ : ScopedTypedStateConcrete Γ σ) :
    ScopedTypedStateConcrete Δ σ' :=
  Cpp.block_body_normal_preserves_scoped_typed_state_concrete hty hσ hready hstep

-- Residual readiness boundaries

theorem seq_left_normal_preserves_body_ready
    {Γ Δ : TypeEnv} {σ σ₁ : State} {s t : CppStmt}
    (htyS : HasTypeStmtCI .normalK Γ s Δ)
    (hready : StmtReadyConcrete Γ σ (.seq s t))
    (hstepS : BigStepStmt σ s .normal σ₁)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    StmtReadyConcrete Δ σ₁ t := by
  exact
    (Cpp.seq_left_normal_preserves_body_ready_concrete
      htyS hready hstepS hσ).2

theorem block_head_normal_preserves_block_ready
    {Γ Δ : TypeEnv} {σ σ₁ : State} {s : CppStmt} {ss : StmtBlock}
    (htyS : HasTypeStmtCI .normalK Γ s Δ)
    (hready : BlockReadyConcrete Γ σ (.cons s ss))
    (hstepS : BigStepStmt σ s .normal σ₁)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    BlockReadyConcrete Δ σ₁ ss := by
  exact
    (Cpp.block_head_normal_preserves_block_ready_concrete
      htyS hready hstepS hσ).2

-- While: current concrete API honestly needs body-normal typing.

theorem while_body_normal_preserves_body_ready_typed
    {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hready : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hstepBody : BigStepStmt σ body .normal σ₁)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    StmtReadyConcrete Γ σ₁ (.whileStmt c body) := by
  exact
    (Cpp.while_body_normal_preserves_body_ready_concrete_typed
      htyWhile hready hstepBody hσ).2

theorem while_body_continue_preserves_body_ready_typed
    {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hready : StmtReadyConcrete Γ σ (.whileStmt c body))
    (hstepBody : BigStepStmt σ body .continueResult σ₁)
    (hσ : ScopedTypedStateConcrete Γ σ) :
    StmtReadyConcrete Γ σ₁ (.whileStmt c body) := by
  exact
    (Cpp.while_body_continue_preserves_body_ready_concrete_typed
      htyWhile hready hstepBody hσ).2

end InternalClosureRoadmapConcrete
end Cpp
