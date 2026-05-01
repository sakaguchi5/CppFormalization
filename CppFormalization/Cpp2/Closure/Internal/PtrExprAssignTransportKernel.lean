import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete

namespace Cpp

/--
Independent transport kernel for the *expression-level* part of the dereference
frontier.

This is intentionally weaker than the old bundled dereference kernel:
it only says that a pointer-valued expression remains ready after an assignment.
It does **not** say that the pointed-to cell remains live or readable.

That split is mathematically important. In the current readiness design,
`ExprReadyConcrete Γ σ e (.ptr τ)` is strictly weaker than
"the dereference of `e` stays valid/readable after assignment".
-/
structure PtrExprAssignTransportKernel : Type where
  ptrExpr_after_assign :
    ∀ {Γ : TypeEnv} {σ σ' : State}
      {q : PlaceExpr} {rhs : ValExpr}
      {e : ValExpr} {τ : CppType},
      ScopedTypedStateConcrete Γ σ' →
      ExprReadyConcrete Γ σ e (.ptr τ) →
      BigStepStmt σ (.assign q rhs) .normal σ' →
      ExprReadyConcrete Γ σ' e (.ptr τ)

/--
Current expression-level pointer replay package.

This remains axiomatic for now, but it is intentionally separated from
pointee-live / dereference-readable transport.
-/
axiom ptrExprAssignTransportKernel : PtrExprAssignTransportKernel

theorem ptr_expr_ready_after_assign
    {Γ : TypeEnv} {σ σ' : State}
    {q : PlaceExpr} {rhs : ValExpr}
    {e : ValExpr} {τ : CppType} :
    ScopedTypedStateConcrete Γ σ' →
    ExprReadyConcrete Γ σ e (.ptr τ) →
    BigStepStmt σ (.assign q rhs) .normal σ' →
    ExprReadyConcrete Γ σ' e (.ptr τ) := by
  intro hσ' hready hstep
  exact ptrExprAssignTransportKernel.ptrExpr_after_assign hσ' hready hstep

end Cpp
