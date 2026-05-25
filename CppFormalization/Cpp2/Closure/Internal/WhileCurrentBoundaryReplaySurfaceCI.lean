import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryReplayTailAdequacyTheoremsCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryReplaySurfaceCI

Bundle the remaining current-boundary while replay surface.

At the previous layer, tail adequacy and dynamic state replay have already been
made theorem-backed:

- post-body `ScopedTypedStateConcrete` comes from preservation;
- normal/continue tail adequacy comes from the current `BodyClosureBoundaryCI`.

The public current-boundary theorem still takes three replay-facing pieces:

- the while header component;
- the body-normal backedge replay component;
- the body-continue backedge replay component.

This file groups them into two meaningful layers:

1. `WhileBackedgeReplayCI`: the normal/continue route replay package;
2. `WhileCurrentBoundaryReplaySurfaceCI`: the header plus backedge replay surface.

C++ reading: once the current `while` boundary is fixed, the remaining
program-facing replay contract says that the loop header is well-typed and both
backedges can reconstruct the next iteration boundary.  The tail recursion is a
separate proof-architecture shell, not a program contract.
-/

/--
The two backedge replay contracts of a `while` loop.

These are the meaningful route-specific residuals after preservation has
supplied the post-state typing facts.
-/
structure WhileBackedgeReplayCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  normalReplay : LoopIterationBoundaryReplayAfterNormalCI Γ c body
  continueReplay : LoopIterationBoundaryReplayAfterContinueCI Γ c body

/--
The current-boundary replay surface for a `while` loop.

This bundles the header information and the two route-level backedge replay
contracts.  It intentionally does not include `htailClosure`: recursion is a
case-driver / proof-architecture concern, not part of the program replay surface.
-/
structure WhileCurrentBoundaryReplaySurfaceCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  header : LoopReentryHeaderCI Γ c
  backedge : WhileBackedgeReplayCI Γ c body

/-- Project the header component from the bundled replay surface. -/
def loopReentryHeaderCI_of_currentBoundaryReplaySurface
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplaySurfaceCI Γ c body) :
    LoopReentryHeaderCI Γ c :=
  S.header

/-- Project the backedge replay component from the bundled replay surface. -/
def whileBackedgeReplayCI_of_currentBoundaryReplaySurface
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplaySurfaceCI Γ c body) :
    WhileBackedgeReplayCI Γ c body :=
  S.backedge

/-- Project normal-route replay from the bundled replay surface. -/
def loopIterationBoundaryReplayAfterNormalCI_of_currentBoundaryReplaySurface
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplaySurfaceCI Γ c body) :
    LoopIterationBoundaryReplayAfterNormalCI Γ c body :=
  S.backedge.normalReplay

/-- Project continue-route replay from the bundled replay surface. -/
def loopIterationBoundaryReplayAfterContinueCI_of_currentBoundaryReplaySurface
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplaySurfaceCI Γ c body) :
    LoopIterationBoundaryReplayAfterContinueCI Γ c body :=
  S.backedge.continueReplay

/-- Reassemble a replay surface from the previously separate components. -/
def whileCurrentBoundaryReplaySurfaceCI_of_components
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hheader : LoopReentryHeaderCI Γ c)
    (hnormalReplay : LoopIterationBoundaryReplayAfterNormalCI Γ c body)
    (hcontinueReplay : LoopIterationBoundaryReplayAfterContinueCI Γ c body) :
    WhileCurrentBoundaryReplaySurfaceCI Γ c body :=
  { header := hheader
    backedge :=
      { normalReplay := hnormalReplay
        continueReplay := hcontinueReplay } }

/-- Eta sanity check for the surface split. -/
theorem whileCurrentBoundaryReplaySurfaceCI_eta_components
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplaySurfaceCI Γ c body) :
    whileCurrentBoundaryReplaySurfaceCI_of_components
      S.header
      S.backedge.normalReplay
      S.backedge.continueReplay = S := by
  cases S with
  | mk header backedge =>
      cases backedge
      rfl

/--
Current-boundary while closure through the bundled replay surface.

Compared with
`while_function_body_closure_boundary_ci_of_currentBoundary_iterationBoundaryReplay_tailAdequacyTheorems`,
this theorem no longer exposes `hheader`, `hnormalReplay`, and
`hcontinueReplay` as unrelated arguments.  They are one replay surface.

The remaining separate input is `htailClosure`, because that is the recursion /
case-driver shell rather than a while replay contract.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_replaySurface_tailAdequacyTheorems
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hsurface : WhileCurrentBoundaryReplaySurfaceCI Γ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_iterationBoundaryReplay_tailAdequacyTheorems
      hentry
      hsurface.header
      hsurface.backedge.normalReplay
      hsurface.backedge.continueReplay
      htailClosure

end Cpp
