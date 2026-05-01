import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Internal.AssignTransportKernel
import CppFormalization.Cpp2.Closure.Internal.PtrExprAssignTransportKernel

namespace Cpp

/-!
After splitting off expression-level pointer replay, the remaining honest
frontier is narrower:

- expression-level pointer readiness is handled by
  `PtrExprAssignTransportKernel`;
- what still remains here is the pointee-live / dereference-readable part.

This is the genuinely alias-sensitive residue.
-/


/--
Remaining dereference frontier after separating pointer-expression replay.

What is left is no longer "pointer expressions stay ready", but the stronger
question:

- if a pointer expression previously supported dereference,
  does it still support dereference after assignment?
- if `load (.deref e)` was readable before assignment,
  can that readable witness be reconstructed afterwards?

These are the parts that are plausibly false without additional
non-interference or stronger pointer invariants, so they stay isolated here.
-/
structure DerefAssignTransportKernel : Type where
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
Current dereference pointee/readable frontier package.

This remains axiomatic for now. The point of the split is that the weaker
expression-level replay is now exposed separately in
`PtrExprAssignTransportKernel`, while the genuinely stronger alias-sensitive
residue stays here.
-/
axiom derefAssignTransportKernel : DerefAssignTransportKernel

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
