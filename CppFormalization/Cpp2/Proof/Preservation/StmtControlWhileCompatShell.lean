import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Proof.Control.StmtControlCompatibility

namespace Cpp

/-!
# Proof.Preservation.StmtControlWhileCompatShell

Open `while` compatibility obligations for `StmtControlKernel`.

These are still honest axioms because the generic compatibility kernel does not
carry the extra data now known to be necessary for theorem-backed `while`
preservation:
- current-state condition readiness,
- loop-body local boundary,
- reentry kernel.

So the kernel file should import these goals rather than define them inline.
-/

axiom while_true_normal_normal_goal
    {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂}
    (hcompBody : StmtControlCompatible hN hbody)
    (hcompTail : StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC) htail) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ₂

axiom while_true_continue_normal_goal
    {Γ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hbody : BigStepStmt σ body .continueResult σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) .normal σ₂}
    (hcompBody : StmtControlCompatible hC hbody)
    (hcompTail : StmtControlCompatible (HasTypeStmtCI.while_normal hc hN hB hC) htail) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Γ σ₂

axiom while_true_normal_return_goal
    {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {rv : Option Value}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hR : HasTypeStmtCI .returnK Γ body Δ}
    {hbody : BigStepStmt σ body .normal σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂}
    (hcompBody : StmtControlCompatible hN hbody)
    (hcompTail : StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR) htail) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Δ σ₂

axiom while_true_continue_return_goal
    {Γ Δ : TypeEnv} {σ σ₁ σ₂ : State} {c : ValExpr} {body : CppStmt}
    {rv : Option Value}
    {hc : HasValueType Γ c (.base .bool)}
    {hN : HasTypeStmtCI .normalK Γ body Γ}
    {hB : HasTypeStmtCI .breakK Γ body Γ}
    {hC : HasTypeStmtCI .continueK Γ body Γ}
    {hR : HasTypeStmtCI .returnK Γ body Δ}
    {hbody : BigStepStmt σ body .continueResult σ₁}
    {htail : BigStepStmt σ₁ (.whileStmt c body) (.returnResult rv) σ₂}
    (hcompBody : StmtControlCompatible hC hbody)
    (hcompTail : StmtControlCompatible (HasTypeStmtCI.while_return hc hN hB hC hR) htail) :
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    ScopedTypedStateConcrete Δ σ₂

end Cpp
