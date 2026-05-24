import CppFormalization.Cpp2.Closure.Internal.LoopBodyDynamicReplayStateTheoremsCI

namespace Cpp

/-!
# Closure.Internal.LoopBodyDynamicReplayContinueStateTheoremsCI

Theorem-backed state component for the continue side of loop-body dynamic replay.

The previous state theorem file discharged the normal-side post-state fact:

- `state_after_normal` : preservation of `ScopedTypedStateConcrete`.

This file does the continue-side analogue:

- `state_after_continue` : preservation of `ScopedTypedStateConcrete`.

The genuinely loop-specific residue is still readiness replay:

- `body_ready_after_normal`;
- `body_ready_after_continue`.

C++ reading: a `continue` from the loop body does not mean the state may stop
being well-scoped/well-typed.  It only changes the control route back to the
while header.  Preservation supplies the post-state typing fact; replay/invariant
work is still needed to show the body is ready again.
-/

/--
The residual continue-side dynamic obligation after state preservation has been
removed: only body readiness replay remains.
-/
structure LoopBodyReadyAfterContinueCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  body_ready_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      StmtReadyConcrete Γ σ' body

/--
Theorem-backed state replay after a body-continue step.

This is statement continue preservation specialized to a loop-body boundary.
The typing witness is `hbody.profile.continueTyping`, and the concrete
preconditions are `hbody.dynamic.state` and `hbody.dynamic.safe`.
-/
def loopBody_state_after_continue_of_preservation
    {Γ : TypeEnv} {body : CppStmt} :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      ScopedTypedStateConcrete Γ σ' := by
  intro σ σ' hbody hstep
  have hC : HasTypeStmtCI .continueK Γ body Γ :=
    hbody.profile.continueTyping
  have hcompBody : StmtControlCompatible hC hstep :=
    stmt_continue_control_compatible_of_normal
      stmt_normal_control_compatible hC hstep
  exact
    stmt_continue_preserves_scoped_typed_state_concrete
      hC hstep hcompBody hbody.dynamic.state hbody.dynamic.safe

/--
Rebuild the continue-side dynamic split from theorem-backed state preservation
plus the genuinely residual body-readiness replay component.
-/
def loopBodyDynamicAfterContinueSplitCI_of_state_preservation
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hready : LoopBodyReadyAfterContinueCI Γ c body) :
    LoopBodyDynamicAfterContinueSplitCI Γ c body :=
  { state_after_continue := by
      intro σ σ' hbody hstep
      exact
        loopBody_state_after_continue_of_preservation
          hbody hstep
    body_ready_after_continue := hready.body_ready_after_continue }

/--
Forget a full continue-side dynamic split to its remaining body-readiness
component.  This is useful when comparing the old and strengthened surfaces.
-/
def loopBodyReadyAfterContinueCI_of_dynamic_split
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (D : LoopBodyDynamicAfterContinueSplitCI Γ c body) :
    LoopBodyReadyAfterContinueCI Γ c body :=
  { body_ready_after_continue := D.body_ready_after_continue }

/--
Current-boundary while closure with both dynamic state components theorem-backed.

Compared with
`while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry`,
this version no longer asks for either full dynamic split.  It asks only for the
remaining normal/continue body-readiness replay components; both scoped/typed
post-state facts are supplied by preservation.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitDynamicReentry_stateTheorems
    (mkWhileReentry : WhileReentryReadyProvider)
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
    (hreadyContinue : LoopBodyReadyAfterContinueCI Γ c body)
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
        mkWhileReentry hreadyNormal)
      hadequacyNormal
      hcondContinue
      (loopBodyDynamicAfterContinueSplitCI_of_state_preservation
        hreadyContinue)
      hadequacyContinue
      hnormal
      hcontinue
      htailClosure

end Cpp
