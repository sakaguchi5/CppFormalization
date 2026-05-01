import CppFormalization.Cpp2.Closure.Internal.StmtControlPreservation
import CppFormalization.Cpp2.Closure.Internal.ReadinessBoundaryConcrete

namespace Cpp
namespace InternalClosureRoadmapConcrete

theorem while_body_normal_preserves_entry_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .normal σ₁) :
    WhileEntryReadyCI Γ σ₁ c body := by
  exact
    (Cpp.while_body_normal_preserves_entry_ready_concrete_typed
      mkWhileReentry hcond hbody K hstepBody).2

theorem while_body_continue_preserves_entry_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .continueResult σ₁) :
    WhileEntryReadyCI Γ σ₁ c body := by
  exact
    (Cpp.while_body_continue_preserves_entry_ready_concrete_typed
      mkWhileReentry hcond hbody K hstepBody).2

theorem while_body_normal_preserves_body_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .normal σ₁) :
    StmtReadyConcrete Γ σ₁ (.whileStmt c body) := by
  exact
    stmtReady_of_whileEntryReady K.hc
      (while_body_normal_preserves_entry_ready_typed
        mkWhileReentry hcond hbody K hstepBody)

theorem while_body_continue_preserves_body_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ₁ : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .continueResult σ₁) :
    StmtReadyConcrete Γ σ₁ (.whileStmt c body) := by
  exact
    stmtReady_of_whileEntryReady K.hc
      (while_body_continue_preserves_entry_ready_typed
        mkWhileReentry hcond hbody K hstepBody)

end InternalClosureRoadmapConcrete
end Cpp
