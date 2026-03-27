import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.PrimitiveStmtNormalPreservation

namespace Cpp

/-!
`ite` の normal-path preservation。
ここではまず generic な分解を axiomatize し、
そのうえで両 branch が primitive normal 文である場合の preservation を theorem として束ねる。
-/

/- =========================================================
   1. typing / readiness / operational 分解
   ========================================================= -/

axiom ite_typing_data
    {Γ Δ : TypeEnv} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.ite c s t) Δ →
    HasTypeStmtCI .normalK Γ s Δ ∧ HasTypeStmtCI .normalK Γ t Δ

axiom ite_ready_branch_data
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {s t : CppStmt} :
    StmtReadyConcrete Γ σ (.ite c s t) →
    StmtReadyConcrete Γ σ s ∧ StmtReadyConcrete Γ σ t

axiom ite_normal_branch_data
    {σ σ' : State} {c : ValExpr} {s t : CppStmt} :
    BigStepStmt σ (.ite c s t) .normal σ' →
    BigStepStmt σ s .normal σ' ∨ BigStepStmt σ t .normal σ'


/- =========================================================
   2. generic theorem from branch subproofs
   ========================================================= -/

theorem ite_normal_preserves_scoped_typed_state_from_branches
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt} :
    HasTypeStmtCI .normalK Γ (.ite c s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.ite c s t) →
    BigStepStmt σ (.ite c s t) .normal σ' →
    (StmtReadyConcrete Γ σ s →
      BigStepStmt σ s .normal σ' →
      ScopedTypedStateConcrete Δ σ') →
    (StmtReadyConcrete Γ σ t →
      BigStepStmt σ t .normal σ' →
      ScopedTypedStateConcrete Δ σ') →
    ScopedTypedStateConcrete Δ σ' := by
  intro hty hσ hready hstep hs ht
  rcases ite_ready_branch_data hready with ⟨hreadyS, hreadyT⟩
  rcases ite_normal_branch_data hstep with hsStep | htStep
  · exact hs hreadyS hsStep
  · exact ht hreadyT htStep


/- =========================================================
   3. primitive branches の corollary
   ========================================================= -/

theorem primitive_branches_ite_normal_preserves_scoped_typed_state_concrete
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt} :
    PrimitiveNormalStmt s →
    PrimitiveNormalStmt t →
    HasTypeStmtCI .normalK Γ (.ite c s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.ite c s t) →
    BigStepStmt σ (.ite c s t) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprimS hprimT hty hσ hready hstep
  rcases ite_typing_data hty with ⟨htyS, htyT⟩
  refine ite_normal_preserves_scoped_typed_state_from_branches
    hty hσ hready hstep ?_ ?_
  · intro hreadyS hsStep
    exact primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprimS htyS hσ hreadyS hsStep
  · intro hreadyT htStep
    exact primitive_stmt_normal_preserves_scoped_typed_state_concrete
      hprimT htyT hσ hreadyT htStep

theorem ite_normal_preserves_scoped_typed_state_concrete_of_primitive_branches
    {Γ Δ : TypeEnv} {σ σ' : State} {c : ValExpr} {s t : CppStmt} :
    PrimitiveNormalStmt s →
    PrimitiveNormalStmt t →
    HasTypeStmtCI .normalK Γ (.ite c s t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.ite c s t) →
    BigStepStmt σ (.ite c s t) .normal σ' →
    ScopedTypedStateConcrete Δ σ' := by
  intro hprimS hprimT hty hσ hready hstep
  exact primitive_branches_ite_normal_preserves_scoped_typed_state_concrete
    hprimS hprimT hty hσ hready hstep

end Cpp
