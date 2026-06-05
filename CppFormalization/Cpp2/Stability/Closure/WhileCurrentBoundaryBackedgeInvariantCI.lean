import CppFormalization.Cpp2.Route.Closure.WhileCurrentBoundaryHeaderTheoremsCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryBackedgeInvariantCI

Name the remaining program-facing replay contract for the current-boundary
`while` theorem.

After the preceding layers:

- post-state scoped/typed facts are theorem-backed by preservation;
- tail adequacy is theorem-backed from the current `BodyClosureBoundaryCI`;
- header typing is theorem-backed from the current `BodyClosureBoundaryCI`;
- full loop-body adequacy replay has been reduced to return-only adequacy replay.

The remaining replay surface is therefore exactly the backedge invariant:

1. concrete next-iteration readiness replay;
2. return-only profile adequacy replay.

C++ reading: after either body reentry route (`normal` or `continue`), the next
iteration must be semantically reusable.  Concretely, the condition/body must be
ready again, and if the next body execution can return then the same loop-body
profile must expose that return channel.
-/

/--
The genuine program-facing backedge invariant for a `while` loop.

This deliberately does not contain the header: header typing is static and is
recovered from the current while boundary.  It also does not contain tail
closure: recursion is proof architecture rather than a loop invariant.
-/
structure WhileBackedgeInvariantCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  ready : WhileBackedgeReadyReplayCI Γ c body
  returnAdequacy : WhileBackedgeReturnAdequacyReplayCI Γ c body

/--
Successor-edge reading of `WhileBackedgeInvariantCI`.

C++ reading:
after the loop body exits by `normal` or `continue`, control returns to the next
iteration.  The condition/body boundary must be replayable at that backedge.

Unlike a plain dynamic successor, this invariant also carries return-channel
adequacy replay for the loop body.
-/
abbrev WhileBackedgeSuccessorInvariantCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type :=
  WhileBackedgeInvariantCI Γ c body

/-- Forget the named backedge invariant to the previous headerless replay surface. -/
def whileCurrentBoundaryReplayHeaderlessSurfaceCI_of_backedgeInvariant
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (I : WhileBackedgeInvariantCI Γ c body) :
    WhileCurrentBoundaryReplayHeaderlessSurfaceCI Γ c body :=
  { ready := I.ready
    returnAdequacy := I.returnAdequacy }

/-- Project the named backedge invariant out of the previous headerless surface. -/
def whileBackedgeInvariantCI_of_headerlessSurface
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplayHeaderlessSurfaceCI Γ c body) :
    WhileBackedgeInvariantCI Γ c body :=
  { ready := S.ready
    returnAdequacy := S.returnAdequacy }

/-- Eta sanity check for the invariant/headerless-surface split. -/
theorem whileCurrentBoundaryReplayHeaderlessSurfaceCI_eta_backedgeInvariant
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplayHeaderlessSurfaceCI Γ c body) :
    whileCurrentBoundaryReplayHeaderlessSurfaceCI_of_backedgeInvariant
      (whileBackedgeInvariantCI_of_headerlessSurface S) = S := by
  cases S
  rfl

/--
Current-boundary while closure through the named backedge invariant.

This is the cleaned current-boundary surface after header theoremization and
return-only adequacy factoring.  The remaining caller-visible pieces are:

- the current while boundary;
- the backedge invariant;
- the tail-recursion shell.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_backedgeInvariant_tailAdequacyTheorems
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hinvariant : WhileBackedgeInvariantCI Γ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_headerlessReturnFactoredReplaySurface_tailAdequacyTheorems
      hentry
      (whileCurrentBoundaryReplayHeaderlessSurfaceCI_of_backedgeInvariant
        hinvariant)
      htailClosure

end Cpp
