import CppFormalization.Cpp2.Stability.Closure.LoopReentryKernelSplitCI

namespace Cpp

/-!
# Closure.Internal.LoopBodyDynamicReplaySplitCI

Split the dynamic part of same-profile loop-body replay.

`LoopBodyAfterNormalSameProfileCI` / `LoopBodyAfterContinueSameProfileCI`
already force the replayed loop-body boundary to reuse the input structural and
profile fields.  Their remaining dynamic field is still bundled as

`LoopBodyDynamicBoundary Γ σ' body`.

This file splits that dynamic field into its two actual obligations:

- `ScopedTypedStateConcrete Γ σ'`
- `StmtReadyConcrete Γ σ' body`

C++ reading:
after a body-normal or body-continue iteration, the next iteration uses the
same static body/profile, but it still requires:
1. the post-state is well typed/scoped;
2. the same body is ready to execute again in that post-state.

These are different proof obligations.  The first is usually preservation; the
second is readiness replay / loop invariant.
-/

/-- Dynamic replay after a body-normal step, split into state and body readiness. -/
structure LoopBodyDynamicAfterNormalSplitCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  state_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      ScopedTypedStateConcrete Γ σ'

  body_ready_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      StmtReadyConcrete Γ σ' body

/-- Dynamic replay after a body-continue step, split into state and body readiness. -/
structure LoopBodyDynamicAfterContinueSplitCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  state_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      ScopedTypedStateConcrete Γ σ'

  body_ready_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      StmtReadyConcrete Γ σ' body

/-- Reassemble post-state dynamic boundary after body-normal from split dynamic obligations. -/
def loopBodyDynamicAfterNormal_of_split
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (D : LoopBodyDynamicAfterNormalSplitCI Γ c body) :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      LoopBodyDynamicBoundary Γ σ' body := by
  intro σ σ' hbody hstep
  exact
    { state := D.state_after_normal hbody hstep
      safe := D.body_ready_after_normal hbody hstep }

/-- Reassemble post-state dynamic boundary after body-continue from split dynamic obligations. -/
def loopBodyDynamicAfterContinue_of_split
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (D : LoopBodyDynamicAfterContinueSplitCI Γ c body) :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyDynamicBoundary Γ σ' body := by
  intro σ σ' hbody hstep
  exact
    { state := D.state_after_continue hbody hstep
      safe := D.body_ready_after_continue hbody hstep }

/--
Same-profile normal replay from split dynamic replay plus same-profile
post-state adequacy.
-/
def loopBodyAfterNormalSameProfileCI_of_dynamic_split
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (D : LoopBodyDynamicAfterNormalSplitCI Γ c body)
    (A :
      ∀ {σ σ' : State},
        (hbody : LoopBodyBoundaryCI Γ σ body) →
        BigStepStmt σ body .normal σ' →
        LoopBodyAdequacyCI Γ σ' body hbody.profile) :
    LoopBodyAfterNormalSameProfileCI Γ c body :=
  { dynamic_after_normal := loopBodyDynamicAfterNormal_of_split D
    adequacy_after_normal := A }

/--
Same-profile continue replay from split dynamic replay plus same-profile
post-state adequacy.
-/
def loopBodyAfterContinueSameProfileCI_of_dynamic_split
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (D : LoopBodyDynamicAfterContinueSplitCI Γ c body)
    (A :
      ∀ {σ σ' : State},
        (hbody : LoopBodyBoundaryCI Γ σ body) →
        BigStepStmt σ body .continueResult σ' →
        LoopBodyAdequacyCI Γ σ' body hbody.profile) :
    LoopBodyAfterContinueSameProfileCI Γ c body :=
  { dynamic_after_continue := loopBodyDynamicAfterContinue_of_split D
    adequacy_after_continue := A }

/--
Current-boundary while closure through split dynamic replay and same-profile
post-state loop-body adequacy.

This is the strengthened target after the same-profile split:
- condition replay remains explicit;
- body replay is split into state preservation, body readiness replay, and
  same-profile loop-body adequacy.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hheader : LoopReentryHeaderCI Γ c)
    (hcondNormal : LoopCondAfterNormalCI Γ c body)
    (hdynNormal : LoopBodyDynamicAfterNormalSplitCI Γ c body)
    (hadequacyNormal :
      ∀ {σ0 σ1 : State},
        (hbody : LoopBodyBoundaryCI Γ σ0 body) →
        BigStepStmt σ0 body .normal σ1 →
        LoopBodyAdequacyCI Γ σ1 body hbody.profile)
    (hcondContinue : LoopCondAfterContinueCI Γ c body)
    (hdynContinue : LoopBodyDynamicAfterContinueSplitCI Γ c body)
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
    while_function_body_closure_boundary_ci_of_currentBoundary_splitSameProfileReentryComponents
      hentry
      hheader
      hcondNormal
      (loopBodyAfterNormalSameProfileCI_of_dynamic_split
        hdynNormal hadequacyNormal)
      hcondContinue
      (loopBodyAfterContinueSameProfileCI_of_dynamic_split
        hdynContinue hadequacyContinue)
      hnormal
      hcontinue
      htailClosure

end Cpp

