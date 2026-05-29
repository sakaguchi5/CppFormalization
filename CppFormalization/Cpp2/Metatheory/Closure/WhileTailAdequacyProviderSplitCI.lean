import CppFormalization.Cpp2.Metatheory.Closure.WhileTailReentryProviderSplitCI

namespace Cpp

/-!
# Closure.Internal.WhileTailAdequacyProviderSplitCI

Split the post-state tail adequacy obligation for `while` into its two actual
channels: body-normal reentry and body-continue reentry.

After the loop-body/profile witness-provider refactor, the normal/continue
post-state adequacy components no longer need to be residual shells.  Both are
theorem-backed directly from the original top-level while adequacy:

- a tail normal step after a body-normal iteration is wrapped by
  `BigStepStmt.whileTrueNormal`;
- a tail return step after a body-normal iteration is wrapped by
  `BigStepStmt.whileTrueNormal`;
- the continue case is analogous, using `BigStepStmt.whileTrueContinue`.

The remaining while debt after this file is therefore not post-state adequacy.
It is the delimiter reentry/dynamic reconstruction side.
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

/--
Theorem-backed post-state top-level while adequacy after one body-normal
iteration.

C++ reading: if the current condition evaluated to true and the body finished
normally, then any subsequent tail-`while` normal/return execution can be
prefixed by that executed iteration.  The original top-level while adequacy
therefore already exposes the needed tail normal/return channels.
-/
def while_tail_adequacy_after_body_normal_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcondTrue : BigStepValue σ c (.bool true))
    (hbodyNormal : BigStepStmt σ body .normal σ1) :
    BodyAdequacyCI Γ σ1 (.whileStmt c body) hentry.static.profile :=
  BodyAdequacyCI.ofWitness
    (normalWitness := by
      intro σ2 htail
      exact hentry.adequacy.normalWitness
        (BigStepStmt.whileTrueNormal hcondTrue hbodyNormal htail))
    (returnWitness := by
      intro rv σ2 htail
      exact hentry.adequacy.returnWitness
        (BigStepStmt.whileTrueNormal hcondTrue hbodyNormal htail))

/--
Theorem-backed post-state top-level while adequacy after one body-continue
iteration.

This is the continue-channel analogue of
`while_tail_adequacy_after_body_normal_of_entry`.
-/
def while_tail_adequacy_after_body_continue_of_entry
    {Γ : TypeEnv} {σ σ1 : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hcondTrue : BigStepValue σ c (.bool true))
    (hbodyContinue : BigStepStmt σ body .continueResult σ1) :
    BodyAdequacyCI Γ σ1 (.whileStmt c body) hentry.static.profile :=
  BodyAdequacyCI.ofWitness
    (normalWitness := by
      intro σ2 htail
      exact hentry.adequacy.normalWitness
        (BigStepStmt.whileTrueContinue hcondTrue hbodyContinue htail))
    (returnWitness := by
      intro rv σ2 htail
      exact hentry.adequacy.returnWitness
        (BigStepStmt.whileTrueContinue hcondTrue hbodyContinue htail))

/-- The theorem-backed normal-post adequacy component. -/
def whileTailNormalAdequacyCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailNormalAdequacyCI hentry :=
  { afterNormal := by
      intro σ1 hcondTrue hbodyNormal
      exact
        while_tail_adequacy_after_body_normal_of_entry
          hentry hcondTrue hbodyNormal }

/-- The theorem-backed continue-post adequacy component. -/
def whileTailContinueAdequacyCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileTailContinueAdequacyCI hentry :=
  { afterContinue := by
      intro σ1 hcondTrue hbodyContinue
      exact
        while_tail_adequacy_after_body_continue_of_entry
          hentry hcondTrue hbodyContinue }

/--
Eta sanity check for the theorem-backed split provider.

The old residual-provider eta theorem intentionally no longer states equality
with `whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI`: the point of this
patch is that normal/continue post-state adequacy is no longer residual.
-/
theorem whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI_eta_post_split
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    whileTailAdequacyProviderCI_of_post_split
        hentry
        (whileTailNormalAdequacyCI_of_bodyClosureBoundaryCI hentry)
        (whileTailContinueAdequacyCI_of_bodyClosureBoundaryCI hentry) =
      { afterNormal := by
          intro σ1 hcondTrue hbodyNormal
          exact
            while_tail_adequacy_after_body_normal_of_entry
              hentry hcondTrue hbodyNormal
        afterContinue := by
          intro σ1 hcondTrue hbodyContinue
          exact
            while_tail_adequacy_after_body_continue_of_entry
              hentry hcondTrue hbodyContinue } := by
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
