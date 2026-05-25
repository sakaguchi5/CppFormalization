import CppFormalization.Cpp2.Closure.Internal.LoopBodyDynamicReplayContinueStateTheoremsCI

namespace Cpp

/-!
# Closure.Internal.LoopBodyIterationReadyReplayCI

Bundle the remaining loop-specific replay obligations after the state part of
dynamic replay has been theorem-backed.

After `LoopBodyDynamicReplayStateTheoremsCI` and
`LoopBodyDynamicReplayContinueStateTheoremsCI`, the scoped/typed post-state facts
are supplied by preservation:

- `state_after_normal`;
- `state_after_continue`.

The remaining dynamic replay obligations are not generic state preservation.
They are exactly next-iteration readiness facts:

- the while condition is ready again;
- the loop body is ready again.

C++ reading: after one body iteration, preservation says the state is still
well-scoped/well-typed.  But re-entering the loop additionally requires that the
program did not destroy the resources needed to evaluate the condition or run the
body again.  That is the loop invariant / replay-stability contract.
-/

/--
Readiness replay for the next iteration after a body-normal step.

This deliberately bundles condition readiness replay and body readiness replay.
The scoped/typed post-state part is not here; it is supplied separately by
preservation.
-/
structure LoopIterationReadyAfterNormalCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  cond_ready_after_normal :
    ∀ {σ σ' : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      ExprReadyConcrete Γ σ' c (.base .bool)

  body_ready_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      StmtReadyConcrete Γ σ' body

/--
Readiness replay for the next iteration after a body-continue step.

This is the continue analogue of `LoopIterationReadyAfterNormalCI`.
-/
structure LoopIterationReadyAfterContinueCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  cond_ready_after_continue :
    ∀ {σ σ' : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      ExprReadyConcrete Γ σ' c (.base .bool)

  body_ready_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      StmtReadyConcrete Γ σ' body

/-- Project condition replay after body-normal from bundled iteration readiness. -/
def loopCondAfterNormalCI_of_iterationReady
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationReadyAfterNormalCI Γ c body) :
    LoopCondAfterNormalCI Γ c body :=
  { cond_after_normal := R.cond_ready_after_normal }

/-- Project body readiness replay after body-normal from bundled iteration readiness. -/
def loopBodyReadyAfterNormalCI_of_iterationReady
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationReadyAfterNormalCI Γ c body) :
    LoopBodyReadyAfterNormalCI Γ c body :=
  { body_ready_after_normal := R.body_ready_after_normal }

/-- Project condition replay after body-continue from bundled iteration readiness. -/
def loopCondAfterContinueCI_of_iterationReady
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationReadyAfterContinueCI Γ c body) :
    LoopCondAfterContinueCI Γ c body :=
  { cond_after_continue := R.cond_ready_after_continue }

/-- Project body readiness replay after body-continue from bundled iteration readiness. -/
def loopBodyReadyAfterContinueCI_of_iterationReady
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationReadyAfterContinueCI Γ c body) :
    LoopBodyReadyAfterContinueCI Γ c body :=
  { body_ready_after_continue := R.body_ready_after_continue }

/--
Current-boundary while closure with state theorem-backed and the remaining
readiness replay bundled by iteration route.

Compared with
`while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry_stateTheorems`,
this theorem no longer asks for condition replay and body readiness replay as
separate arguments.  Each route gets one C++-meaningful contract:

- after body-normal, the next iteration is ready;
- after body-continue, the next iteration is ready.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_iterationReady_stateTheorems
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hheader : LoopReentryHeaderCI Γ c)
    (hreadyNormal : LoopIterationReadyAfterNormalCI Γ c body)
    (hadequacyNormal :
      ∀ {σ0 σ1 : State},
        (hbody : LoopBodyBoundaryCI Γ σ0 body) →
        BigStepStmt σ0 body .normal σ1 →
        LoopBodyAdequacyCI Γ σ1 body hbody.profile)
    (hreadyContinue : LoopIterationReadyAfterContinueCI Γ c body)
    (hadequacyContinue :
      ∀ {σ0 σ1 : State},
        (hbody : LoopBodyBoundaryCI Γ σ0 body) →
        BigStepStmt σ0 body .continueResult σ1 →
        LoopBodyAdequacyCI Γ σ1 body hbody.profile)
    (hnormal : WhileTailNormalAdequacyCI hentry)
    (hcontinue : WhileTailContinueAdequacyCI hentry)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry_stateTheorems
      hentry
      hheader
      (loopCondAfterNormalCI_of_iterationReady hreadyNormal)
      (loopBodyReadyAfterNormalCI_of_iterationReady hreadyNormal)
      hadequacyNormal
      (loopCondAfterContinueCI_of_iterationReady hreadyContinue)
      (loopBodyReadyAfterContinueCI_of_iterationReady hreadyContinue)
      hadequacyContinue
      hnormal
      hcontinue
      htailClosure

end Cpp
