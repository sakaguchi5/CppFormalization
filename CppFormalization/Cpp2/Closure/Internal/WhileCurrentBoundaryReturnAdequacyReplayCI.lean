import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryReplayFactoredSurfaceCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryReturnAdequacyReplayCI

Split the adequacy-replay part of the current-boundary while replay surface so
that only the genuinely path-sensitive return component remains residual.

At the previous layer, `WhileBackedgeAdequacyReplayCI` asked for full
same-profile `LoopBodyAdequacyCI` after the body-normal and body-continue
backedges.  That was too coarse as an audit surface:

- normal / break / continue adequacy are available from the closed slots of the
  loop-body profile;
- return adequacy is path-sensitive, because the post-state may make a return
  branch reachable even if the current body iteration did not return.

This file keeps return adequacy replay as the explicit residual and rebuilds the
full adequacy replay package theoremically from it.

C++ reading: after a normal or continue backedge, the remaining semantic
profile obligation is not "all adequacy again"; it is only this:
if the next execution of the same body can return, the same loop-body profile
must expose a return channel for that return.
-/

/--
Build full loop-body adequacy from the closed normal/break/continue profile slots
plus a return-adequacy provider.

This is the core local theorem behind the split: the only genuinely residual
part of `LoopBodyAdequacyCI` is the return channel.
-/
def loopBodyAdequacyCI_of_returnProvider
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (hreturn : LoopBodyReturnAdequacyProviderCI Γ σ body P) :
    LoopBodyAdequacyCI Γ σ body P :=
  LoopBodyAdequacyCI.ofWitness
    (normalWitness := by
      intro _σ' _hstep
      rcases P.normalClosed with ⟨hN, hEq⟩
      exact ⟨⟨Γ, hN⟩, hEq⟩)
    (breakWitness := by
      intro _σ' _hstep
      rcases P.breakClosed with ⟨hB, hEq⟩
      exact ⟨⟨Γ, hB⟩, hEq⟩)
    (continueWitness := by
      intro _σ' _hstep
      rcases P.continueClosed with ⟨hC, hEq⟩
      exact ⟨⟨Γ, hC⟩, hEq⟩)
    (returnWitness := by
      intro rv σ' hstep
      exact hreturn.returnWitness hstep)

/--
Return adequacy provider from either an exposed return channel in the profile or
semantic exclusion of body returns from the current state.

This helper packages the two natural ways to discharge the return residual.
-/
noncomputable def loopBodyReturnAdequacyProviderCI_of_returnOut_or_noReturn
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    {P : LoopBodyControlProfile Γ body}
    (h :
      (∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
        P.summary.returnOut = some out) ∨
      (∀ {rv : Option Value} {σ' : State},
        ¬ BigStepStmt σ body (.returnResult rv) σ')) :
    LoopBodyReturnAdequacyProviderCI Γ σ body P := by
  classical
  let hex :
      ∃ R : LoopBodyReturnAdequacyProviderCI Γ σ body P, True := by
    cases h with
    | inl hout =>
        exact ⟨loopBodyReturnAdequacyProviderCI_of_returnOut hout, trivial⟩
    | inr hno =>
        exact ⟨loopBodyReturnAdequacyProviderCI_of_noReturn hno, trivial⟩
  exact Classical.choose hex

/--
Return-profile-or-no-return residual after a body-normal step.

This is an alternative, proof-friendly presentation of the return adequacy
residual.  It says that after a normal backedge either the same profile exposes a
return channel, or the next body execution cannot return.
-/
structure LoopBodyReturnProfileOrNoReturnAfterNormalCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  return_profile_or_noReturn_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
        (∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
          hbody.profile.summary.returnOut = some out) ∨
        (∀ {rv : Option Value} {σ2 : State},
          ¬ BigStepStmt σ' body (.returnResult rv) σ2)

/--
Return-profile-or-no-return residual after a body-continue step.
-/
structure LoopBodyReturnProfileOrNoReturnAfterContinueCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  return_profile_or_noReturn_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
        (∃ out : {Δ : TypeEnv // HasTypeStmtCI .returnK Γ body Δ},
          hbody.profile.summary.returnOut = some out) ∨
        (∀ {rv : Option Value} {σ2 : State},
          ¬ BigStepStmt σ' body (.returnResult rv) σ2)

/--
Turn the normal-route profile/no-return residual into the direct return provider
surface.
-/
noncomputable def loopBodyReturnAdequacyReplayAfterNormalCI_of_profileOrNoReturn
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopBodyReturnProfileOrNoReturnAfterNormalCI Γ c body) :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      LoopBodyReturnAdequacyProviderCI Γ σ' body hbody.profile := by
  intro σ σ' hbody hstep
  exact
    loopBodyReturnAdequacyProviderCI_of_returnOut_or_noReturn
      (R.return_profile_or_noReturn_after_normal hbody hstep)

/--
Turn the continue-route profile/no-return residual into the direct return
provider surface.
-/
noncomputable def loopBodyReturnAdequacyReplayAfterContinueCI_of_profileOrNoReturn
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : LoopBodyReturnProfileOrNoReturnAfterContinueCI Γ c body) :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyReturnAdequacyProviderCI Γ σ' body hbody.profile := by
  intro σ σ' hbody hstep
  exact
    loopBodyReturnAdequacyProviderCI_of_returnOut_or_noReturn
      (R.return_profile_or_noReturn_after_continue hbody hstep)

/--
The direct return-adequacy replay residual for both while backedges.

This is the semantically precise replacement for full adequacy replay:
normal/break/continue adequacy are theorem-backed from the profile; return
adequacy remains path-sensitive and is exposed here.
-/
structure WhileBackedgeReturnAdequacyReplayCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  return_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      LoopBodyReturnAdequacyProviderCI Γ σ' body hbody.profile

  return_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyReturnAdequacyProviderCI Γ σ' body hbody.profile

/-- Build the direct return-replay residual from profile/no-return witnesses. -/
noncomputable def whileBackedgeReturnAdequacyReplayCI_of_profileOrNoReturn
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (N : LoopBodyReturnProfileOrNoReturnAfterNormalCI Γ c body)
    (C : LoopBodyReturnProfileOrNoReturnAfterContinueCI Γ c body) :
    WhileBackedgeReturnAdequacyReplayCI Γ c body :=
  { return_after_normal :=
      loopBodyReturnAdequacyReplayAfterNormalCI_of_profileOrNoReturn N
    return_after_continue :=
      loopBodyReturnAdequacyReplayAfterContinueCI_of_profileOrNoReturn C }

/--
Rebuild full same-profile adequacy replay from return-only adequacy replay.

This is the main theoremization step of this file.
-/
def whileBackedgeAdequacyReplayCI_of_returnReplay
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (R : WhileBackedgeReturnAdequacyReplayCI Γ c body) :
    WhileBackedgeAdequacyReplayCI Γ c body :=
  { body_adequacy_after_normal := by
      intro σ σ' hbody hstep
      exact
        loopBodyAdequacyCI_of_returnProvider
          (R.return_after_normal hbody hstep)
    body_adequacy_after_continue := by
      intro σ σ' hbody hstep
      exact
        loopBodyAdequacyCI_of_returnProvider
          (R.return_after_continue hbody hstep) }

/--
Current-boundary replay surface where adequacy replay has been reduced to the
return-only residual.

The header remains visible here because the purpose of this layer is the return
split, not header theoremization.
-/
structure WhileCurrentBoundaryReplayReturnFactoredSurfaceCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  header : LoopReentryHeaderCI Γ c
  ready : WhileBackedgeReadyReplayCI Γ c body
  returnAdequacy : WhileBackedgeReturnAdequacyReplayCI Γ c body

/-- Forget the return-factored surface to the previous factored surface. -/
def whileCurrentBoundaryReplayFactoredSurfaceCI_of_returnFactored
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryReplayReturnFactoredSurfaceCI Γ c body) :
    WhileCurrentBoundaryReplayFactoredSurfaceCI Γ c body :=
  { header := S.header
    ready := S.ready
    adequacy :=
      whileBackedgeAdequacyReplayCI_of_returnReplay S.returnAdequacy }

/--
Current-boundary while closure through the return-factored replay surface.

The remaining replay obligations are now:
- header;
- concrete next-iteration readiness replay;
- return-only adequacy replay.

The recursion shell stays separate.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_returnFactoredReplaySurface_tailAdequacyTheorems
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hsurface : WhileCurrentBoundaryReplayReturnFactoredSurfaceCI Γ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_factoredReplaySurface_tailAdequacyTheorems
      hentry
      (whileCurrentBoundaryReplayFactoredSurfaceCI_of_returnFactored hsurface)
      htailClosure

end Cpp
