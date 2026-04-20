import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel

namespace Cpp

/-!
After theoremizing the replay-stable primitive fragment and then extending the
suffix fragment to declaration cases, the remaining honest frontier is no longer
"seq/block in general". It is the dereference / alias-sensitive part of assign
transport.

This file does not pretend to solve that frontier. It isolates it.

The key observation is that the bundled `AssignTransportKernel` already covers:
- replay of the assigned lhs/rhs pair itself;
- replay-stable variable-place transport;
- readable transport for replay-stable variable loads.

What still remains is the assign transport needed for suffixes whose readiness
depends on dereference-based places.
-/


/--
Pointer-valued expression transport needed to replay dereference-based places
across an assignment step.

This is intentionally phrased at the expression / value / place boundary rather
than as a blanket statement about arbitrary expressions:
the missing part of the theory is specifically about preserving pointer
evaluation and the live/readable cell it points to.
-/
structure DerefAssignTransportKernel : Type where
  /--
  A pointer-valued expression that is ready before the assignment remains ready
  afterwards.
  -/
  ptrExpr_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType},
      ScopedTypedStateConcrete Γ σ' →
      ExprReadyConcrete Γ σ e (.ptr τ) →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ExprReadyConcrete Γ σ' e (.ptr τ)

  /--
  If a pointer expression actually points to some live `τ`-cell before the
  assignment, then after the assignment it still points to some live `τ`-cell.
  The post-address is allowed to differ: alias-sensitive heads may update the
  pointer value itself.
  -/
  ptrValueReadyAt_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType} {a : Nat},
      ScopedTypedStateConcrete Γ σ' →
      PtrValueReadyAt Γ σ e τ a →
      CellLiveTyped σ a τ →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ∃ a', PtrValueReadyAt Γ σ' e τ a' ∧ CellLiveTyped σ' a' τ

  /--
  The readable witness needed for `load (.deref e)` can be reconstructed after
  assignment.
  -/
  derefLoadReadable_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType},
      ScopedTypedStateConcrete Γ σ' →
      (∃ a, BigStepPlace σ (.deref e) a ∧ CellReadableTyped σ a τ) →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ∃ a', BigStepPlace σ' (.deref e) a' ∧ CellReadableTyped σ' a' τ

/--
Current dereference frontier package.

This remains axiomatic for now. The point of introducing it is to make the
remaining gap explicit and local, instead of leaving it hidden behind the
general residual-readiness axioms.
-/
axiom derefAssignTransportKernel : DerefAssignTransportKernel

theorem ptr_expr_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ e (.ptr τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ExprReadyConcrete Γ σ' e (.ptr τ) := by
  intro hσ' hready hstep
  exact derefAssignTransportKernel.ptrExpr_after_assign hσ' hready hstep

theorem ptr_value_ready_at_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} {a : Nat} :
    ScopedTypedStateConcrete Γ σ' →
    PtrValueReadyAt Γ σ e τ a →
    CellLiveTyped σ a τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ∃ a', PtrValueReadyAt Γ σ' e τ a' ∧ CellLiveTyped σ' a' τ := by
  intro hσ' hptr hlive hstep
  exact derefAssignTransportKernel.ptrValueReadyAt_after_assign
    hσ' hptr hlive hstep

theorem deref_place_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ (.deref e) τ →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    PlaceReadyConcrete Γ σ' (.deref e) τ := by
  intro hσ' hready hstep
  cases hready with
  | deref hptr hlive =>
      rcases ptr_value_ready_at_after_assign hσ' hptr hlive hstep with
        ⟨a', hptr', hlive'⟩
      exact PlaceReadyConcrete.deref hptr' hlive'

theorem deref_load_readable_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ (.deref e) a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    (∃ a', BigStepPlace σ' (.deref e) a' ∧ CellReadableTyped σ' a' τ) := by
  intro hσ' hread hstep
  exact derefAssignTransportKernel.derefLoadReadable_after_assign
    hσ' hread hstep

end Cpp
