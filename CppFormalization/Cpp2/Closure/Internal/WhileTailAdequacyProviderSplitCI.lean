import CppFormalization.Cpp2.Closure.Internal.WhileTailReentryProviderSplitCI

namespace Cpp

/-!
# Closure.Internal.WhileTailAdequacyProviderSplitCI

Split the post-state tail adequacy obligation for `while` into its two actual
channels: body-normal reentry and body-continue reentry.

This is intentionally more aggressive than merely exposing
`WhileTailAdequacyProviderCI` as a single component.  The current-boundary while
case now sees the exact residual obligations that remain after delimiter
reentry:

- after a `normal` body step, rebuild adequacy for the tail `while`;
- after a `continue` body step, rebuild adequacy for the tail `while`.

The existing lower-layer declaration
`whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI` is still used only as the
source of the two current shell components.  The point of this file is to make
those two components the new surface for the next theoremization step.
-/

/-- Post-state tail adequacy after a normal body iteration. -/
structure WhileTailNormalAdequacyCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) : Type where
  afterNormal :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .normal σ1 →
      BodyAdequacyCI Γ σ1 (.whileStmt c body) hentry.static.profile

/-- Post-state tail adequacy after a continue body iteration. -/
structure WhileTailContinueAdequacyCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) : Type where
  afterContinue :
    ∀ {σ1 : State},
      BigStepValue σ c (.bool true) →
      BigStepStmt σ body .continueResult σ1 →
      BodyAdequacyCI Γ σ1 (.whileStmt c body) hentry.static.profile

/-- Reassemble the old tail adequacy provider from the split normal/continue pieces. -/
def whileTailAdequacyProviderCI_of_post_split
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hnormal : WhileTailNormalAdequacyCI hentry)
    (hcontinue : WhileTailContinueAdequacyCI hentry) :
    WhileTailAdequacyProviderCI Γ σ c body hentry.static :=
  { afterNormal := by
      intro σ1 hcondTrue hbodyNormal
      exact hnormal.afterNormal hcondTrue hbodyNormal
    afterContinue := by
      intro σ1 hcondTrue hbodyContinue
      exact hcontinue.afterContinue hcondTrue hbodyContinue }

/-- The current residual normal-post adequacy component. -/
noncomputable def whileTailNormalAdequacyCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailNormalAdequacyCI hentry :=
  { afterNormal := by
      intro σ1 hcondTrue hbodyNormal
      exact
        (whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry).afterNormal
          hcondTrue hbodyNormal }

/-- The current residual continue-post adequacy component. -/
noncomputable def whileTailContinueAdequacyCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailContinueAdequacyCI hentry :=
  { afterContinue := by
      intro σ1 hcondTrue hbodyContinue
      exact
        (whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry).afterContinue
          hcondTrue hbodyContinue }

/--
Eta sanity check for the current residual adequacy provider through direct
normal/continue projections.
-/
theorem whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI_eta_post_split
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry =
      whileTailAdequacyProviderCI_of_post_split
        hentry
        { afterNormal := by
            intro σ1 hcondTrue hbodyNormal
            exact
              (whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry).afterNormal
                hcondTrue hbodyNormal }
        { afterContinue := by
            intro σ1 hcondTrue hbodyContinue
            exact
              (whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry).afterContinue
                hcondTrue hbodyContinue } := by
  cases whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry
  rfl

/--
Current-boundary while closure through delimiter reentry plus split post-state
adequacy obligations.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitPostAdequacy
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hreentry : LoopReentryKernelCI Γ c body)
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
    while_function_body_closure_boundary_ci_of_currentBoundary_splitProvider
      hentry
      hreentry
      (whileTailAdequacyProviderCI_of_post_split hentry hnormal hcontinue)
      htailClosure

/--
Current-boundary while closure through the three currently exposed residual
components:
- delimiter reentry;
- normal-post tail adequacy;
- continue-post tail adequacy.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitPostComponents
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_splitPostAdequacy
      hentry
      (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)
      (whileTailNormalAdequacyCI_of_bodyClosureBoundaryCI hentry)
      (whileTailContinueAdequacyCI_of_bodyClosureBoundaryCI hentry)
      htailClosure

end Cpp
