import CppFormalization.Cpp2.Closure.Internal.ResidualTransportStrongThinSeparatedDeclarationsFragment

namespace Cpp

/-!
Standard theorem surface for the assign-headed residual transport story.

At this point the project has two assignment-headed fragments:
- `AssignHeadTransportableStmt / Block` for the non-declaration suffix fragment;
- `AssignHeadTransportableStmtDecl / BlockDecl` for the declaration-aware one.

Mathematically, the declaration-aware fragment is the larger / standard one.
This file makes that relationship explicit and provides direct seq/block residual
theorems in a form that downstream files can use without choosing between the
two layers every time.
-/


/- =========================================================
   1. Coercion from the non-declaration fragment to the declaration-aware one
   ========================================================= -/
mutual

def AssignHeadTransportableStmt.toDecl
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} :
    {st : CppStmt} →
    AssignHeadTransportableStmt Γ σ q rhs st →
    AssignHeadTransportableStmtDecl Γ σ q rhs st
  | _, .skip =>
      .skip
  | _, .exprStmt hc hty =>
      .exprStmt hc hty
  | _, .assign hp hc hty =>
      .assign hp hc hty
  | _, .seq hs ht =>
      .seq hs.toDecl ht.toDecl
  | _, .ite hc hs ht =>
      .ite hc hs.toDecl ht.toDecl
  | _, .whileStmt hc hbody =>
      .whileStmt hc hbody.toDecl
  | _, .block hblock =>
      .block hblock.toDecl
  | _, .breakStmt =>
      .breakStmt
  | _, .continueStmt =>
      .continueStmt
  | _, .returnNone =>
      .returnNone
  | _, .returnSome hc hty =>
      .returnSome hc hty

def AssignHeadTransportableBlock.toDecl
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} :
    {ss : StmtBlock} →
    AssignHeadTransportableBlock Γ σ q rhs ss →
    AssignHeadTransportableBlockDecl Γ σ q rhs ss
  | _, .nil =>
      .nil
  | _, .cons hs hss =>
      .cons hs.toDecl hss.toDecl

end

@[simp] theorem AssignHeadTransportableStmt_toDecl_skip
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} :
    (AssignHeadTransportableStmt.skip :
      AssignHeadTransportableStmt Γ σ q rhs .skip).toDecl =
      AssignHeadTransportableStmtDecl.skip := by
  rfl

@[simp] theorem AssignHeadTransportableBlock_toDecl_nil
    {Γ : TypeEnv} {σ : State} {q : PlaceExpr} {rhs : ValExpr} :
    (AssignHeadTransportableBlock.nil :
      AssignHeadTransportableBlock Γ σ q rhs .nil).toDecl =
      AssignHeadTransportableBlockDecl.nil := by
  rfl


/- =========================================================
   2. Standard direct theorem surface: declaration-aware version
   ========================================================= -/

theorem assign_head_decl_stmt_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {st : CppStmt} :
    AssignHeadTransportableStmtDecl Γ σ q rhs st →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' st := by
  intro htransport hσ' hready hstep
  exact assign_head_transportable_decl_stmt_ready_after_assign_head
    htransport hσ' hready hstep

theorem assign_head_decl_block_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlockDecl Γ σ q rhs ss →
    ScopedTypedStateConcrete Γ σ' →
    BlockReadyConcrete Γ σ ss →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BlockReadyConcrete Γ σ' ss := by
  intro htransport hσ' hready hstep
  exact assign_head_transportable_decl_block_ready_after_assign_head
    htransport hσ' hready hstep

/--
Statement-level replay bridge for block bodies.

The raw block transport theorem already exists in the declaration-aware fragment.
What was missing was the pushed-scope bridge connecting that raw block replay to
`StmtReadyConcrete Γ σ (.block ss)`.
-/
theorem assign_head_decl_block_stmt_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlockDecl Γ σ q rhs ss →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.block ss) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.block ss) := by
  intro htransport hσ' hready hstep
  exact assign_head_transportable_decl_stmt_ready_after_assign_head
    (.block (assign_head_transportable_decl_block_pushScope htransport))
    hσ' hready hstep

theorem assign_head_block_stmt_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlock Γ σ q rhs ss →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ (.block ss) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' (.block ss) := by
  intro htransport hσ' hready hstep
  exact assign_head_decl_block_stmt_ready_after_assign
    htransport.toDecl hσ' hready hstep

theorem assign_head_decl_seq_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {t : CppStmt} :
    AssignHeadTransportableStmtDecl Γ σ q rhs t →
    HasTypeStmtCI .normalK Γ (.seq (.assign q rhs) t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq (.assign q rhs) t) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro htransport hty hσ hready hstep
  exact assign_head_transportable_decl_right_seq_normal_preserves_residual_boundary
    htransport hty hσ hready hstep

theorem assign_head_decl_block_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlockDecl Γ σ q rhs ss →
    HasTypeBlockCI .normalK Γ (.cons (.assign q rhs) ss) Θ →
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ (.cons (.assign q rhs) ss) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ConsResidualBoundary Θ σ' ss := by
  intro htransport hty hσ hready hstep
  exact assign_head_transportable_decl_tail_cons_head_normal_preserves_residual_boundary
    htransport hty hσ hready hstep


/- =========================================================
   3. Convenience corollaries: non-declaration fragment via coercion
   ========================================================= -/

theorem assign_head_stmt_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {st : CppStmt} :
    AssignHeadTransportableStmt Γ σ q rhs st →
    ScopedTypedStateConcrete Γ σ' →
    StmtReadyConcrete Γ σ st →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    StmtReadyConcrete Γ σ' st := by
  intro htransport hσ' hready hstep
  exact assign_head_decl_stmt_ready_after_assign
    htransport.toDecl hσ' hready hstep

theorem assign_head_block_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlock Γ σ q rhs ss →
    ScopedTypedStateConcrete Γ σ' →
    BlockReadyConcrete Γ σ ss →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    BlockReadyConcrete Γ σ' ss := by
  intro htransport hσ' hready hstep
  exact assign_head_decl_block_ready_after_assign
    htransport.toDecl hσ' hready hstep

theorem assign_head_seq_residual_boundary
    {Γ Δ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {t : CppStmt} :
    AssignHeadTransportableStmt Γ σ q rhs t →
    HasTypeStmtCI .normalK Γ (.seq (.assign q rhs) t) Δ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.seq (.assign q rhs) t) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    SeqResidualBoundary Δ σ' t := by
  intro htransport hty hσ hready hstep
  exact assign_head_decl_seq_residual_boundary
    htransport.toDecl hty hσ hready hstep

theorem assign_head_block_seq_residual_boundary
    {Γ Θ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr} {ss : StmtBlock} :
    AssignHeadTransportableBlock Γ σ q rhs ss →
    HasTypeBlockCI .normalK Γ (.cons (.assign q rhs) ss) Θ →
    ScopedTypedStateConcrete Γ σ →
    BlockReadyConcrete Γ σ (.cons (.assign q rhs) ss) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ConsResidualBoundary Θ σ' ss := by
  intro htransport hty hσ hready hstep
  exact assign_head_decl_block_residual_boundary
    htransport.toDecl hty hσ hready hstep

end Cpp
