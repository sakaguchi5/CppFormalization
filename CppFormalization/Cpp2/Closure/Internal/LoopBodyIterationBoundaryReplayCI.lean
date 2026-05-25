import CppFormalization.Cpp2.Closure.Internal.LoopBodyIterationReadyReplayCI

namespace Cpp

/-!
# Closure.Internal.LoopBodyIterationBoundaryReplayCI

Bundle the remaining per-iteration replay data after the scoped/typed state
component has been theorem-backed.

At this point the dynamic replay split has three conceptual pieces:

- post-state `ScopedTypedStateConcrete`, supplied by preservation;
- next-iteration readiness, bundled by `LoopIterationReadyAfterNormalCI` /
  `LoopIterationReadyAfterContinueCI`;
- same-profile loop-body adequacy in the post-state.

This file bundles the last two into a route-level replay contract.

C++ reading: after a body `normal` or `continue` step, preservation says the
state is still well-scoped/well-typed.  The remaining program-specific invariant
is that the next iteration can actually be reconstructed: the condition can be
evaluated again, the same body is ready again, and the same loop-body profile is
adequate in the post-state.
-/

/--
Route-level replay contract after a body-normal step.

This is the current meaningful residual for the normal reentry route:
next-iteration readiness plus same-profile loop-body adequacy.
-/
structure LoopIterationBoundaryReplayAfterNormalCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  ready : LoopIterationReadyAfterNormalCI Γ c body
  body_adequacy_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      LoopBodyAdequacyCI Γ σ' body hbody.profile

/--
Route-level replay contract after a body-continue step.

This is the continue analogue of `LoopIterationBoundaryReplayAfterNormalCI`.
-/
structure LoopIterationBoundaryReplayAfterContinueCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  ready : LoopIterationReadyAfterContinueCI Γ c body
  body_adequacy_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyAdequacyCI Γ σ' body hbody.profile

/-- Project next-iteration readiness from normal-route boundary replay. -/
def loopIterationReadyAfterNormalCI_of_boundaryReplay
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationBoundaryReplayAfterNormalCI Γ c body) :
    LoopIterationReadyAfterNormalCI Γ c body :=
  R.ready

/-- Project next-iteration readiness from continue-route boundary replay. -/
def loopIterationReadyAfterContinueCI_of_boundaryReplay
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationBoundaryReplayAfterContinueCI Γ c body) :
    LoopIterationReadyAfterContinueCI Γ c body :=
  R.ready

/--
Build the same-profile normal replay component from route-level boundary replay.

The state part is supplied by preservation; readiness and adequacy come from the
route-level replay contract.
-/
def loopBodyAfterNormalSameProfileCI_of_iterationBoundaryReplay
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationBoundaryReplayAfterNormalCI Γ c body) :
    LoopBodyAfterNormalSameProfileCI Γ c body :=
  loopBodyAfterNormalSameProfileCI_of_dynamic_split
    (loopBodyDynamicAfterNormalSplitCI_of_state_preservation
      (loopBodyReadyAfterNormalCI_of_iterationReady R.ready))
    R.body_adequacy_after_normal

/--
Build the same-profile continue replay component from route-level boundary replay.

The state part is supplied by preservation; readiness and adequacy come from the
route-level replay contract.
-/
def loopBodyAfterContinueSameProfileCI_of_iterationBoundaryReplay
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopIterationBoundaryReplayAfterContinueCI Γ c body) :
    LoopBodyAfterContinueSameProfileCI Γ c body :=
  loopBodyAfterContinueSameProfileCI_of_dynamic_split
    (loopBodyDynamicAfterContinueSplitCI_of_state_preservation
      (loopBodyReadyAfterContinueCI_of_iterationReady R.ready))
    R.body_adequacy_after_continue

/--
Current-boundary while closure with state theorem-backed and the remaining
normal/continue replay obligations bundled as route-level boundary replay.

Compared with
`while_function_body_closure_boundary_ci_of_currentBoundary_iterationReady_stateTheorems`,
this theorem no longer asks for readiness replay and loop-body post-state
adequacy as separate arguments.  Each reentry route gets one residual contract:

- body-normal route: next iteration boundary replay;
- body-continue route: next iteration boundary replay.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_iterationBoundaryReplay_stateTheorems
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hheader : LoopReentryHeaderCI Γ c)
    (hnormalReplay : LoopIterationBoundaryReplayAfterNormalCI Γ c body)
    (hcontinueReplay : LoopIterationBoundaryReplayAfterContinueCI Γ c body)
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
    while_function_body_closure_boundary_ci_of_currentBoundary_iterationReady_stateTheorems
      hentry
      hheader
      hnormalReplay.ready
      hnormalReplay.body_adequacy_after_normal
      hcontinueReplay.ready
      hcontinueReplay.body_adequacy_after_continue
      hnormal
      hcontinue
      htailClosure

end Cpp
