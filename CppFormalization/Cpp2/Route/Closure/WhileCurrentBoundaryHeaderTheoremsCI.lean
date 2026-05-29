import CppFormalization.Cpp2.Adequacy.Closure.WhileCurrentBoundaryReturnAdequacyReplayCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryHeaderTheoremsCI

Theorem-backed header component for the current-boundary while replay surface.

After `WhileCurrentBoundaryReturnAdequacyReplayCI`, the current replay surface has
three program-facing fields:

- header typing for the while condition;
- concrete next-iteration readiness replay;
- return-only adequacy replay.

The header component is not a genuine residual.  A current
`BodyClosureBoundaryCI Γ σ (.whileStmt c body)` already contains enough static
entry information to recover the condition typing through
`whileEntryBoundaryCI_of_bodyClosureBoundaryCI`.

C++ reading: if the current `while (c) body` boundary is known, then `c` is
already known to be a boolean condition.  This is static typing, not a loop
invariant.
-/

/-- Project the reentry-header component from a theorem-backed current while entry. -/
def loopReentryHeaderCI_of_whileEntryBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hcurrent : WhileEntryBoundaryCI Γ σ c body) :
    LoopReentryHeaderCI Γ c :=
  { hc := hcurrent.hc }

/--
The current while boundary theoremically supplies the reentry-header component.

This is the header analogue of the earlier tail-adequacy theoremization: callers
no longer need to supply `LoopReentryHeaderCI Γ c` as a separate replay residual.
-/
def loopReentryHeaderCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopReentryHeaderCI Γ c :=
  loopReentryHeaderCI_of_whileEntryBoundaryCI
    (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry)

/--
The remaining current-boundary replay surface after header theoremization.

Only the genuine backedge-facing obligations remain:

- concrete next-iteration readiness replay;
- return-only adequacy replay.

The header is supplied separately from `hentry`, and the recursion shell remains
outside this surface.
-/
structure WhileCurrentBoundaryReplayHeaderlessSurfaceCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  ready : WhileBackedgeReadyReplayCI Γ c body
  returnAdequacy : WhileBackedgeReturnAdequacyReplayCI Γ c body

/--
Rebuild the return-factored surface by filling the header theoremically from the
current while boundary.
-/
def whileCurrentBoundaryReplayReturnFactoredSurfaceCI_of_headerless
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (S : WhileCurrentBoundaryReplayHeaderlessSurfaceCI Γ c body) :
    WhileCurrentBoundaryReplayReturnFactoredSurfaceCI Γ c body :=
  { header := loopReentryHeaderCI_of_bodyClosureBoundaryCI hentry
    ready := S.ready
    returnAdequacy := S.returnAdequacy }

/-- Project the headerless replay surface out of the return-factored surface. -/
def whileCurrentBoundaryReplayHeaderlessSurfaceCI_of_returnFactored
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplayReturnFactoredSurfaceCI Γ c body) :
    WhileCurrentBoundaryReplayHeaderlessSurfaceCI Γ c body :=
  { ready := S.ready
    returnAdequacy := S.returnAdequacy }

/--
Current-boundary while closure with the header component theorem-backed from
`hentry`.

The remaining replay surface now contains only:

- concrete next-iteration readiness replay;
- return-only adequacy replay.

The tail recursion shell remains separate because it is proof architecture, not a
program replay contract.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_headerlessReturnFactoredReplaySurface_tailAdequacyTheorems
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hsurface : WhileCurrentBoundaryReplayHeaderlessSurfaceCI Γ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_returnFactoredReplaySurface_tailAdequacyTheorems
      hentry
      (whileCurrentBoundaryReplayReturnFactoredSurfaceCI_of_headerless
        hentry hsurface)
      htailClosure

end Cpp
