import CppFormalization.Cpp2.Closure.Internal.AssignHeadResidualTransportTheorems
import CppFormalization.Cpp2.Closure.Internal.WhileNormalPreservation

namespace Cpp

/-!
Standard theorem surface for the assign-headed `while` story.

`AssignHeadResidualTransportTheorems` already standardizes the seq/block residual
surface. This file provides the matching `while`-level entry points, so
downstream proofs do not need to reach for the older specialized theorem names.

Important:
- the head step is still fixed to `.assign q rhs`;
- condition replay uses `StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool)`;
- body replay uses the standard assign-headed transportable fragment, preferably
  the declaration-aware one.
-/


/- =========================================================
   1. Standard declaration-aware while reentry surface
   ========================================================= -/

theorem while_ready_after_assign_head_of_decl_transportable_body
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {c : ValExpr} {body : CppStmt} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    AssignHeadTransportableStmtDecl Γ σ q rhs body →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hc hbody htyWhile hσ' hreadyWhile hstepHead
  have hreadyBody : StmtReadyConcrete Γ σ body :=
    while_ready_body_data hreadyWhile
  have hreadyBody' : StmtReadyConcrete Γ σ' body :=
    assign_head_decl_stmt_ready_after_assign
      hbody hσ' hreadyBody hstepHead
  have hcondReady0 : ExprReadyConcrete Γ σ c (.base .bool) :=
    (while_ready_cond_data hreadyWhile).2
  have hcondReady' : ExprReadyConcrete Γ σ' c (.base .bool) :=
    strongThinSeparated_cond_expr_ready_after_assign
      hc hσ' hcondReady0 hstepHead
  rcases while_typing_data htyWhile with ⟨_, hcb, _, _, _⟩
  exact StmtReadyConcrete.whileStmt hcb hcondReady' hreadyBody'

theorem while_ready_after_assign_head_of_transportable_body
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {c : ValExpr} {body : CppStmt} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    AssignHeadTransportableStmt Γ σ q rhs body →
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  intro hc hbody htyWhile hσ' hreadyWhile hstepHead
  exact while_ready_after_assign_head_of_decl_transportable_body
    hc hbody.toDecl htyWhile hσ' hreadyWhile hstepHead


/- =========================================================
   2. Specialized corollaries for seq/block-shaped bodies
   ========================================================= -/

theorem while_ready_after_assign_head_of_decl_transportable_seq_body
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {c : ValExpr} {s t : CppStmt} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    AssignHeadTransportableStmtDecl Γ σ q rhs (.seq s t) →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.seq s t)) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c (.seq s t)) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c (.seq s t)) := by
  intro hc hbody htyWhile hσ' hreadyWhile hstepHead
  exact while_ready_after_assign_head_of_decl_transportable_body
    hc hbody htyWhile hσ' hreadyWhile hstepHead


theorem while_ready_after_assign_head_of_decl_transportable_block_body
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {c : ValExpr} {ss : StmtBlock} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    AssignHeadTransportableBlockDecl Γ σ q rhs ss →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.block ss)) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c (.block ss)) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c (.block ss)) := by
  intro hc hblock htyWhile hσ' hreadyWhile hstepHead
  have hreadyBlock0 : BlockReadyConcrete (pushTypeScope Γ) (pushScope σ) ss := by
    have hreadyBody : StmtReadyConcrete Γ σ (.block ss) :=
      while_ready_body_data hreadyWhile
    cases hreadyBody with
    | block hreadyBlock =>
        exact hreadyBlock
  have hcondReady0 : ExprReadyConcrete Γ σ c (.base .bool) :=
    (while_ready_cond_data hreadyWhile).2
  have hcondReady' : ExprReadyConcrete Γ σ' c (.base .bool) :=
    strongThinSeparated_cond_expr_ready_after_assign
      hc hσ' hcondReady0 hstepHead
  sorry
  /-
  have hreadyBlock' : BlockReadyConcrete Γ σ' ss :=
    assign_head_decl_block_ready_after_assign
      hblock hσ' hreadyBlock0 hstepHead

  rcases while_typing_data htyWhile with ⟨_, hcb, _, _, _⟩
  exact StmtReadyConcrete.whileStmt hcb hcondReady' (StmtReadyConcrete.block hreadyBlock')
-/
theorem while_ready_after_assign_head_of_transportable_block_body
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {c : ValExpr} {ss : StmtBlock} :
    StrongThinSeparatedCondExpr Γ σ q rhs c (.base .bool) →
    AssignHeadTransportableBlock Γ σ q rhs ss →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.block ss)) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c (.block ss)) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c (.block ss)) := by
  intro hc hblock htyWhile hσ' hreadyWhile hstepHead
  exact while_ready_after_assign_head_of_decl_transportable_block_body
    hc hblock.toDecl htyWhile hσ' hreadyWhile hstepHead


/- =========================================================
   3. Compatibility corollary with the older specialized assign-body theorem
   ========================================================= -/

/--
This theorem is a compatibility bridge.

It does not delete the older specialized theorem
`while_ready_after_body_normal_of_strongThinSeparated_assign`, because that
theorem is strictly weaker in assumptions: it does not require the body itself
to be an assign-headed transportable suffix.

Instead, this corollary says: whenever the body `.assign q rhs` *does* fit the
standard transportable surface, the new standard theorem recovers the same kind
of while reentry result.
-/
theorem while_ready_after_assign_head_of_transportable_assign_body
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs c : ValExpr} {p : PlaceExpr} :
    StrongThinSeparatedCondExpr Γ σ p rhs c (.base .bool) →
    AssignHeadTransportableStmt Γ σ p rhs (.assign q rhs) →
    HasTypeStmtCI .normalK Γ (.whileStmt c (.assign q rhs)) Γ →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.whileStmt c (.assign q rhs)) →
    BigStepStmt σ (.assign p rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.whileStmt c (.assign q rhs)) := by
  intro hc hbody htyWhile hσ' hreadyWhile hstepHead
  exact while_ready_after_assign_head_of_transportable_body
    hc hbody htyWhile hσ' hreadyWhile hstepHead

end Cpp
