import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryReplaySurfaceCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryReplayFactoredSurfaceCI

Factor the bundled current-boundary replay surface into two audit-relevant
backedge layers.

`WhileCurrentBoundaryReplaySurfaceCI` is already the right public surface shape:

- a while header component;
- a normal/continue backedge replay package.

However, the backedge replay package itself still mixes two different kinds of
residual data:

1. next-iteration readiness replay;
2. same-profile loop-body adequacy replay at the post-state.

This file does not remove either component.  It makes the distinction explicit,
so the remaining obligations can be audited separately:

- readiness replay is the direct C++ loop-invariant / replay-stability contract;
- adequacy replay is the semantic-package transport/reconstruction obligation.

C++ reading: after a body-normal or body-continue route, preservation already
supplies the scoped/typed post-state.  The program-facing invariant says the next
condition and body are ready again.  Separately, the semantic proof package must
show that the same loop-body profile is adequate at the post-state.
-/

/--
The readiness-replay part of the two while backedges.

This is the most direct C++ loop-invariant component: after either reentry
route, the next condition/body execution is ready.
-/
structure WhileBackedgeReadyReplayCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  normalReady : LoopIterationReadyAfterNormalCI Γ c body
  continueReady : LoopIterationReadyAfterContinueCI Γ c body

/--
The same-profile adequacy-replay part of the two while backedges.

This is separated from readiness because it is a semantic package transport /
reconstruction obligation rather than merely concrete readiness.
-/
structure WhileBackedgeAdequacyReplayCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  body_adequacy_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      LoopBodyAdequacyCI Γ σ' body hbody.profile

  body_adequacy_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyAdequacyCI Γ σ' body hbody.profile

/-- Reassemble the route-level backedge replay package from factored parts. -/
def whileBackedgeReplayCI_of_ready_adequacy
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : WhileBackedgeReadyReplayCI Γ c body)
    (A : WhileBackedgeAdequacyReplayCI Γ c body) :
    WhileBackedgeReplayCI Γ c body :=
  { normalReplay :=
      { ready := R.normalReady
        body_adequacy_after_normal := A.body_adequacy_after_normal }
    continueReplay :=
      { ready := R.continueReady
        body_adequacy_after_continue := A.body_adequacy_after_continue } }

/-- Project the readiness-replay part out of route-level backedge replay. -/
def whileBackedgeReadyReplayCI_of_backedgeReplay
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (B : WhileBackedgeReplayCI Γ c body) :
    WhileBackedgeReadyReplayCI Γ c body :=
  { normalReady := B.normalReplay.ready
    continueReady := B.continueReplay.ready }

/-- Project the adequacy-replay part out of route-level backedge replay. -/
def whileBackedgeAdequacyReplayCI_of_backedgeReplay
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (B : WhileBackedgeReplayCI Γ c body) :
    WhileBackedgeAdequacyReplayCI Γ c body :=
  { body_adequacy_after_normal := B.normalReplay.body_adequacy_after_normal
    body_adequacy_after_continue := B.continueReplay.body_adequacy_after_continue }

/-- Eta sanity check for factored backedge replay. -/
theorem whileBackedgeReplayCI_eta_ready_adequacy
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (B : WhileBackedgeReplayCI Γ c body) :
    whileBackedgeReplayCI_of_ready_adequacy
        (whileBackedgeReadyReplayCI_of_backedgeReplay B)
        (whileBackedgeAdequacyReplayCI_of_backedgeReplay B) = B := by
  cases B with
  | mk normalReplay continueReplay =>
      cases normalReplay
      cases continueReplay
      rfl

/--
A factored current-boundary replay surface.

This is not meant to replace the simpler bundled surface everywhere.  Its role is
inspection: the header, concrete readiness replay, and semantic adequacy replay
are visible as distinct obligations.
-/
structure WhileCurrentBoundaryReplayFactoredSurfaceCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  header : LoopReentryHeaderCI Γ c
  ready : WhileBackedgeReadyReplayCI Γ c body
  adequacy : WhileBackedgeAdequacyReplayCI Γ c body

/-- Forget the factored replay surface to the bundled replay surface. -/
def whileCurrentBoundaryReplaySurfaceCI_of_factored
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplayFactoredSurfaceCI Γ c body) :
    WhileCurrentBoundaryReplaySurfaceCI Γ c body :=
  { header := S.header
    backedge := whileBackedgeReplayCI_of_ready_adequacy S.ready S.adequacy }

/-- Split the bundled replay surface into the factored audit surface. -/
def whileCurrentBoundaryReplayFactoredSurfaceCI_of_surface
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplaySurfaceCI Γ c body) :
    WhileCurrentBoundaryReplayFactoredSurfaceCI Γ c body :=
  { header := S.header
    ready := whileBackedgeReadyReplayCI_of_backedgeReplay S.backedge
    adequacy := whileBackedgeAdequacyReplayCI_of_backedgeReplay S.backedge }

/-- Eta sanity check for the factored surface. -/
theorem whileCurrentBoundaryReplaySurfaceCI_eta_factored
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplaySurfaceCI Γ c body) :
    whileCurrentBoundaryReplaySurfaceCI_of_factored
      (whileCurrentBoundaryReplayFactoredSurfaceCI_of_surface S) = S := by
  cases S with
  | mk header backedge =>
      dsimp [whileCurrentBoundaryReplaySurfaceCI_of_factored,
        whileCurrentBoundaryReplayFactoredSurfaceCI_of_surface]
      rw [whileBackedgeReplayCI_eta_ready_adequacy]

/--
Current-boundary while closure through the factored replay surface.

Compared with
`while_function_body_closure_boundary_ci_of_currentBoundary_replaySurface_tailAdequacyTheorems`,
this theorem exposes the remaining replay surface in the audit-friendly shape:

- header;
- concrete next-iteration readiness replay;
- same-profile semantic adequacy replay.

The recursion shell remains separate.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_factoredReplaySurface_tailAdequacyTheorems
    (mkWhileReentry : WhileReentryReadyProvider)
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hsurface : WhileCurrentBoundaryReplayFactoredSurfaceCI Γ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_replaySurface_tailAdequacyTheorems
      mkWhileReentry
      hentry
      (whileCurrentBoundaryReplaySurfaceCI_of_factored hsurface)
      htailClosure

end Cpp
