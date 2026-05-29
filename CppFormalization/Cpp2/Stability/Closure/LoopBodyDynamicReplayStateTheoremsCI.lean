import CppFormalization.Cpp2.Stability.Closure.LoopBodyDynamicReplaySplitCI
import CppFormalization.Cpp2.Metatheory.Closure.Unclassified.ReadinessBoundaryConcrete

namespace Cpp

/-!
# Closure.Internal.LoopBodyDynamicReplayStateTheoremsCI

Theorem-backed state component for loop-body dynamic replay.

`LoopBodyDynamicAfterNormalSplitCI` deliberately split the post-body dynamic
obligation into:

- `state_after_normal` : preservation of `ScopedTypedStateConcrete`;
- `body_ready_after_normal`  : replay of `StmtReadyConcrete` for the next body run.

This file discharges the first component from the existing statement normal
preservation theorem.  The remaining normal-side dynamic residual is therefore
only body-readiness replay.

C++ reading: if the loop body is well typed at the loop environment, the input
state is scoped/typed, the body is ready, and the body executes normally, then
the post-state is still scoped/typed.  This is preservation, not a loop
invariant.
-/

/--
The residual normal-side dynamic obligation after state preservation has been
removed: only body readiness replay remains.
-/
structure LoopBodyReadyAfterNormalCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  body_ready_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      StmtReadyConcrete Γ σ' body

/--
Theorem-backed state replay after a body-normal step.

This is exactly statement normal preservation specialized to the loop-body
boundary.  The typing witness is `hbody.profile.normalTyping`, and the concrete
preconditions are `hbody.dynamic.state` and `hbody.dynamic.safe`.
-/
def loopBody_state_after_normal_of_preservation
    {Γ : TypeEnv} {body : CppStmt} :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      ScopedTypedStateConcrete Γ σ' := by
  intro σ σ' hbody hstep
  exact
    stmt_normal_preserves_scoped_typed_state_concrete
      hbody.profile.normalTyping
      hbody.dynamic.state
      hbody.dynamic.safe
      hstep

/--
Rebuild the normal-side dynamic split from theorem-backed state preservation
plus the genuinely residual body-readiness replay component.
-/
def loopBodyDynamicAfterNormalSplitCI_of_state_preservation
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hready : LoopBodyReadyAfterNormalCI Γ c body) :
    LoopBodyDynamicAfterNormalSplitCI Γ c body :=
  { state_after_normal := by
      intro σ σ' hbody hstep
      exact
        loopBody_state_after_normal_of_preservation
          hbody hstep
    body_ready_after_normal := hready.body_ready_after_normal }

/--
Forget a full normal-side dynamic split to its remaining body-readiness
component.  This is useful when comparing the old and strengthened surfaces.
-/
def loopBodyReadyAfterNormalCI_of_dynamic_split
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (D : LoopBodyDynamicAfterNormalSplitCI Γ c body) :
    LoopBodyReadyAfterNormalCI Γ c body :=
  { body_ready_after_normal := D.body_ready_after_normal }

/--
Current-boundary while closure with `state_after_normal` theorem-backed.

Compared with
`while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry`,
this version no longer asks for the full normal-side dynamic split.  It asks
only for the genuinely residual normal-side body-readiness replay, while the
normal post-state scoped/typed fact is supplied by preservation.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry_stateAfterNormalTheorem
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hheader : LoopReentryHeaderCI Γ c)
    (hcondNormal : LoopCondAfterNormalCI Γ c body)
    (hreadyNormal : LoopBodyReadyAfterNormalCI Γ c body)
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
    while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry
      hentry
      hheader
      hcondNormal
      (loopBodyDynamicAfterNormalSplitCI_of_state_preservation
        hreadyNormal)
      hadequacyNormal
      hcondContinue
      hdynContinue
      hadequacyContinue
      hnormal
      hcontinue
      htailClosure

end Cpp
