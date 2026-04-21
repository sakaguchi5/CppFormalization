import CppFormalization.Cpp2.Closure.Internal.AssignHeadWhileTransportTheorems
import CppFormalization.Cpp2.Closure.Internal.WhileNormalPreservation

namespace Cpp

/-!
Compatibility shell for older weak assign-body `while` theorems.

Use `AssignHeadWhileTransportTheorems` first when the body fits the standard
assign-headed transportable surface. This file only re-exports the remaining
weaker specialized assign-body theorems under standard-style names.
-/

/--
Weak assign-body reentry surface.

This is the standard-name wrapper for the older specialized theorem
`while_ready_after_body_normal_of_strongThinSeparated_assign`.
It is strictly weaker than the transportable-body entry point because it does
not require the body itself to satisfy `AssignHeadTransportableStmt`.
-/
theorem while_ready_after_assign_head_of_strongThinSeparated_assign_body
    {Γ : TypeEnv} {σ σ' : State}
    {c : ValExpr} {q : PlaceExpr} {rhs : ValExpr} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.assign q rhs)) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c (.assign q rhs)) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c (.assign q rhs)) := by
  intro hc htyWhile hσ' hreadyWhile hstepBody
  exact while_ready_after_body_normal_of_strongThinSeparated_assign
    hc htyWhile hσ' hreadyWhile hstepBody

/--
Weak assign-body preservation surface.

This is the standard-name wrapper for the older specialized theorem
`strongThinSeparated_assign_body_while_normal_preserves_scoped_typed_state_concrete`.
-/
theorem while_normal_preserves_scoped_typed_state_concrete_of_strongThinSeparated_assign_body
    {Γ Δ : TypeEnv} {σ σ' : State}
    {c : ValExpr} {q : PlaceExpr} {rhs : ValExpr} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.assign q rhs)) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c (.assign q rhs)) →
    BigStepStmt σ (.whileStmt c (.assign q rhs)) .normal σ' →
    WhileTailClosed Γ σ' c (.assign q rhs) →
    ScopedTypedStateConcrete Δ σ' := by
  intro hc htyWhile hσ hready hstep htail
  exact strongThinSeparated_assign_body_while_normal_preserves_scoped_typed_state_concrete
    hc htyWhile hσ hready hstep htail

end Cpp
