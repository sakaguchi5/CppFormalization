/- CppFormalization/Cpp2/Closure/Internal/WhileReentryReadyKernelCI.lean -/
import CppFormalization.Cpp2.Closure.Foundation.Readiness
import CppFormalization.Cpp2.Closure.Foundation.StateInvariantConcrete
import CppFormalization.Cpp2.Closure.Foundation.TypingCI
import CppFormalization.Cpp2.Closure.Internal.WhileDecompositionFacts
import CppFormalization.Cpp2.Closure.Internal.LoopReentryKernelCI

namespace Cpp

/--
Pure dynamic entry data for a `while` header at a concrete state.
This is the minimal payload needed to rebuild `StmtReadyConcrete` for the
same `while` after one body step.
-/
structure WhileEntryReadyCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Prop where
  condReady : ExprReadyConcrete Γ σ c (.base .bool)
  bodyReady : StmtReadyConcrete Γ σ body

@[simp] theorem whileEntryReady_of_stmtReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    WhileEntryReadyCI Γ σ c body := by
  intro h
  rcases while_ready_cond_data h with ⟨_hc, hcond⟩
  exact ⟨hcond, while_ready_body_data h⟩

@[simp] theorem stmtReady_of_whileEntryReady
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (h : WhileEntryReadyCI Γ σ c body) :
    StmtReadyConcrete Γ σ (.whileStmt c body) := by
  exact StmtReadyConcrete.whileStmt hc h.condReady h.bodyReady

/--
A state-indexed reentry kernel for preservation support.

This is intentionally smaller than `LoopReentryKernelCI`:
it does not expose any post-state loop-body boundary; it only reconstructs
the next-entry readiness needed by the tail `while`.
-/
structure WhileReentryReadyAt
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  after_normal :
    ∀ {σ' : State},
      BigStepStmt σ body .normal σ' →
      WhileEntryReadyCI Γ σ' c body
  after_continue :
    ∀ {σ' : State},
      BigStepStmt σ body .continueResult σ' →
      WhileEntryReadyCI Γ σ' c body

abbrev WhileReentryReadyProvider : Type :=
  ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt},
    HasValueType Γ c (.base .bool) →
    HasTypeStmtCI .normalK Γ body Γ →
    HasTypeStmtCI .breakK Γ body Γ →
    HasTypeStmtCI .continueK Γ body Γ →
    ScopedTypedStateConcrete Γ σ →
    StmtReadyConcrete Γ σ (.whileStmt c body) →
    WhileReentryReadyAt Γ σ c body

theorem whileStmtReady_after_normal
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (K : WhileReentryReadyAt Γ σ c body)
    (hstep : BigStepStmt σ body .normal σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  exact stmtReady_of_whileEntryReady hc (K.after_normal hstep)

theorem whileStmtReady_after_continue
    {Γ : TypeEnv} {σ σ' : State} {c : ValExpr} {body : CppStmt}
    (hc : HasValueType Γ c (.base .bool))
    (K : WhileReentryReadyAt Γ σ c body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    StmtReadyConcrete Γ σ' (.whileStmt c body) := by
  exact stmtReady_of_whileEntryReady hc (K.after_continue hstep)

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
