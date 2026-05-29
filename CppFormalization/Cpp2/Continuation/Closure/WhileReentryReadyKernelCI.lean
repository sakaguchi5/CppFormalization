import CppFormalization.Cpp2.Continuation.While.WhileReentryReady
import CppFormalization.Cpp2.Stability.Closure.LoopReentryKernelCI

namespace Cpp

/-!
# Closure.Internal.WhileReentryReadyKernelCI

Compatibility / bridge layer from the closure-level loop reentry kernel to the
lightweight preservation-facing reentry provider.

The lightweight definitions themselves now live in
`Proof.Preservation.WhileReentryReady`, so `Proof.Preservation.StmtControlKernelSupport`
can avoid importing `Closure.Internal` just to obtain `WhileReentryReadyProvider`.
-/

theorem whileEntryReady_after_normal_of_loopReentry
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstep : BigStepStmt σ body .normal σ') :
    WhileEntryReadyCI Γ σ' c body := by
  refine ⟨?_, ?_⟩
  · exact K.cond_after_normal hcond hbody hstep
  · exact (K.nextBody_after_normal hbody hstep).dynamic.safe

theorem whileEntryReady_after_continue_of_loopReentry
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    WhileEntryReadyCI Γ σ' c body := by
  refine ⟨?_, ?_⟩
  · exact K.cond_after_continue hcond hbody hstep
  · exact (K.nextBody_after_continue hbody hstep).dynamic.safe

def WhileReentryReadyAt.of_loopReentry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body) :
    WhileReentryReadyAt Γ σ c body where
  after_normal := fun {_σ'} hstep =>
    whileEntryReady_after_normal_of_loopReentry hcond hbody K hstep
  after_continue := fun {_σ'} hstep =>
    whileEntryReady_after_continue_of_loopReentry hcond hbody K hstep

end Cpp
