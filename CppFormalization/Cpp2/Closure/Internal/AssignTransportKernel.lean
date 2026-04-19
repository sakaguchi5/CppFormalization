import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/--
Read-places whose readiness witness is intended to be transportable across an
assignment step without committing to full alias-sensitive replay for arbitrary
places.

Current base kernel keeps only variable places. This is the honest fragment:
reassigning memory may change the safety of dereference-based places, so they
are excluded until a stronger alias/points-to theory is available.
-/
inductive ReplayStableReadPlace : PlaceExpr → Prop where
  | var {x : Ident} :
      ReplayStableReadPlace (.var x)

/--
A bundled transport kernel for assignment steps.

This does **not** claim that arbitrary statement or expression readiness is
preserved across arbitrary assignments. It only bundles the transport facts that
the current mainline actually treats as primitive:
- self replay for the assigned lhs/rhs pair
- transport of replay-stable read-place readiness
- transport of `load` readability for replay-stable read-places
-/
structure AssignTransportKernel : Type where
  selfPlace_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p : PlaceExpr} {e : ValExpr} {τ : CppType},
      ScopedTypedStateConcrete Γ σ' →
      PlaceReadyConcrete Γ σ p τ →
      BigStepStmt σ (.assign p e) .normal σ' →
      PlaceReadyConcrete Γ σ' p τ

  selfExpr_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p : PlaceExpr} {e : ValExpr} {τ : CppType},
      HasValueType Γ e τ →
      ScopedTypedStateConcrete Γ σ' →
      ExprReadyConcrete Γ σ e τ →
      BigStepStmt σ (.assign p e) .normal σ' →
      ExprReadyConcrete Γ σ' e τ

  stableReadPlace_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p q : PlaceExpr} {e : ValExpr} {τ : CppType},
      ReplayStableReadPlace p →
      ScopedTypedStateConcrete Γ σ' →
      PlaceReadyConcrete Γ σ p τ →
      BigStepStmt σ (.assign q e) .normal σ' →
      PlaceReadyConcrete Γ σ' p τ

  stableLoadReadable_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {p q : PlaceExpr} {e : ValExpr} {τ : CppType},
      ReplayStableReadPlace p →
      ScopedTypedStateConcrete Γ σ' →
      (∃ a, BigStepPlace σ p a ∧ CellReadableTyped σ a τ) →
      BigStepStmt σ (.assign q e) .normal σ' →
      (∃ a, BigStepPlace σ' p a ∧ CellReadableTyped σ' a τ)

/--
Current primitive transport package.

It remains axiomatic at this stage, but the important architectural change is
that the primitive transport obligations now live behind one bundled kernel
instead of four unrelated top-level axioms spread across different files.
-/
axiom assignTransportKernel : AssignTransportKernel

theorem assign_place_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ p τ →
    BigStepStmt σ (.assign p e) .normal σ' →
    PlaceReadyConcrete Γ σ' p τ := by
  intro hσ' hpready hstep
  exact assignTransportKernel.selfPlace_after_assign hσ' hpready hstep

theorem assign_expr_ready_replay_concrete
    {Γ : TypeEnv} {σ σ' : State}
    {p : PlaceExpr} {e : ValExpr} {τ : CppType} :
    HasValueType Γ e τ →
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ e τ →
    BigStepStmt σ (.assign p e) .normal σ' →
    ExprReadyConcrete Γ σ' e τ := by
  intro hty hσ' heready hstep
  exact assignTransportKernel.selfExpr_after_assign hty hσ' heready hstep

theorem replay_stable_read_place_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {p q : PlaceExpr} {e : ValExpr} {τ : CppType} :
    ReplayStableReadPlace p →
    ScopedTypedStateConcrete Γ σ' →
    PlaceReadyConcrete Γ σ p τ →
    BigStepStmt σ (.assign q e) .normal σ' →
    PlaceReadyConcrete Γ σ' p τ := by
  intro hpstable hσ' hpready hstep
  exact assignTransportKernel.stableReadPlace_after_assign
    hpstable hσ' hpready hstep

theorem replay_stable_load_readable_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {p q : PlaceExpr} {e : ValExpr} {τ : CppType} :
    ReplayStableReadPlace p →
    ScopedTypedStateConcrete Γ σ' →
    (∃ a, BigStepPlace σ p a ∧ CellReadableTyped σ a τ) →
    BigStepStmt σ (.assign q e) .normal σ' →
    (∃ a, BigStepPlace σ' p a ∧ CellReadableTyped σ' a τ) := by
  intro hpstable hσ' hread hstep
  exact assignTransportKernel.stableLoadReadable_after_assign
    hpstable hσ' hread hstep

end Cpp
