import CppFormalization.Cpp2.Closure.Internal.LoopBodyIterationBoundaryReplayCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryReplayTailAdequacyTheoremsCI

Hide the already theorem-backed tail-adequacy components from the current
while-closure replay surface.

After the route-level replay split, the public current-boundary theorem still
accepted two tail-adequacy arguments:

- `WhileTailNormalAdequacyCI hentry`;
- `WhileTailContinueAdequacyCI hentry`.

But these are no longer genuine user/program contracts.  They are theorem-backed
from the original `BodyClosureBoundaryCI` for the current while entry via
`whileTailNormalAdequacyCI_of_bodyClosureBoundaryCI` and
`whileTailContinueAdequacyCI_of_bodyClosureBoundaryCI`.

C++ reading: once the current `while` boundary is known, tail adequacy after a
normal or continue body iteration is just operational prefixing of the already
known top-level while adequacy.  The meaningful residuals are now the header
component, the two route-level replay contracts, and the tail-closure recursion.
-/

/--
Current-boundary while closure with:

- state replay theorem-backed by preservation;
- tail adequacy theorem-backed from the current while boundary;
- remaining per-route replay bundled as normal/continue boundary replay.

This is the next compressed surface after
`while_function_body_closure_boundary_ci_of_currentBoundary_iterationBoundaryReplay_stateTheorems`.
It no longer asks callers to supply `WhileTailNormalAdequacyCI` or
`WhileTailContinueAdequacyCI` explicitly.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_iterationBoundaryReplay_tailAdequacyTheorems
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hheader : LoopReentryHeaderCI Γ c)
    (hnormalReplay : LoopIterationBoundaryReplayAfterNormalCI Γ c body)
    (hcontinueReplay : LoopIterationBoundaryReplayAfterContinueCI Γ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_iterationBoundaryReplay_stateTheorems
      mkWhileReentry
      hentry
      hheader
      hnormalReplay
      hcontinueReplay
      (whileTailNormalAdequacyCI_of_bodyClosureBoundaryCI hentry)
      (whileTailContinueAdequacyCI_of_bodyClosureBoundaryCI hentry)
      htailClosure

end Cpp
