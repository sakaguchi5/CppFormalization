import CppFormalization.Cpp2.Closure.Foundation.BodyBoundaryCompatibility
import CppFormalization.Cpp2.Closure.Internal.InternalClosureRoadmapConcrete
import CppFormalization.Cpp2.Closure.Internal.FunctionBodyClosureCI

namespace Cpp
namespace InternalClosureRoadmapCI

theorem while_body_normal_preserves_entry_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .normal σ') :
    WhileEntryReadyCI Γ σ' c body :=
  InternalClosureRoadmapConcrete.while_body_normal_preserves_entry_ready_typed
    mkWhileReentry hcond hbody K hstepBody

theorem while_body_continue_preserves_entry_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .continueResult σ') :
    WhileEntryReadyCI Γ σ' c body :=
  InternalClosureRoadmapConcrete.while_body_continue_preserves_entry_ready_typed
    mkWhileReentry hcond hbody K hstepBody

theorem while_body_normal_preserves_stmt_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  stmtReady_of_whileEntryReady K.hc
    (while_body_normal_preserves_entry_ready_typed
      mkWhileReentry hcond hbody K hstepBody)

theorem while_body_continue_preserves_stmt_ready_typed
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hcond : ExprReadyConcrete Γ σ c (.base .bool))
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (K : LoopReentryKernelCI Γ c body)
    (hstepBody : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) :=
  stmtReady_of_whileEntryReady K.hc
    (while_body_continue_preserves_entry_ready_typed
      mkWhileReentry hcond hbody K hstepBody)

end InternalClosureRoadmapCI
end Cpp
