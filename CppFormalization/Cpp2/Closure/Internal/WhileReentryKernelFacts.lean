import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.LoopBodyBoundaryCI
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI

namespace Cpp

def WhileTailClosed
    (Γ : TypeEnv) (σ' : State) (c : ValExpr) (body : CppStmt) : Prop :=
  ∀ {σ1},
    ScopedTypedStateConcrete Γ σ1 →
    StmtReadyConcrete Γ σ1 (.whileStmt c body) →
    BigStepStmt σ1 (.whileStmt c body) .normal σ' →
    ScopedTypedStateConcrete Γ σ'

theorem while_ready_after_body_normal_via_reentry
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_normal hcond hbody hstep

theorem while_ready_after_body_continue_via_reentry
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_continue hcond hbody hstep

theorem while_ready_after_body_normal_of_kernel
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_normal hcond hbody hstep

theorem while_ready_after_body_continue_of_kernel
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body)
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  K.whileReady_after_continue hcond hbody hstep

end Cpp
