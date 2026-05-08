import CppFormalization.Cpp2.Closure.Internal.WhileTailAdequacyProviderSplitCI

namespace Cpp

/-!
# Closure.Internal.LoopReentryKernelSplitCI

Expose the dynamic reentry obligations inside `LoopReentryKernelCI`.

The previous split established that normal/continue post-state tail adequacy is
theorem-backed from the original top-level while adequacy.  The remaining while
debt is now the delimiter reentry/dynamic reconstruction side.

This file keeps `LoopReentryKernelCI` as the canonical compatibility kernel, but
also introduces a stronger same-profile reentry surface.

Why the extra surface?

`LoopReentryKernelCI.body_after_normal` returns some
`LoopBodyBoundaryCI Γ σ' body`; its type does not say that the returned boundary
reuses the old `structural` and `profile` fields.  C++-semantically, however,
one more iteration of the same `while` executes the same body under the same
static loop-body profile.  Only the dynamic state/readiness and post-state
adequacy should be reconstructed.

So this file exposes two layers:

1. the existing coarse compatibility components:
   - `LoopBodyAfterNormalCI`;
   - `LoopBodyAfterContinueCI`;

2. the stronger same-profile target components:
   - `LoopBodyAfterNormalSameProfileCI`;
   - `LoopBodyAfterContinueSameProfileCI`.

The same-profile components are the preferred theoremization targets.  They
forget to the existing coarse components by rebuilding the post-state boundary
with:

```
structural := hbody.structural
profile    := hbody.profile
```

This makes the intended equality true by construction, not by a later proof.
-/

/-- Static header typing for a reentering while condition. -/
structure LoopReentryHeaderCI
    (Γ : TypeEnv) (c : ValExpr) : Type where
  hc : HasValueType Γ c (.base .bool)

/-- Condition replay after a body-normal step. -/
structure LoopCondAfterNormalCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  cond_after_normal :
    ∀ {σ σ' : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .normal σ' →
      ExprReadyConcrete Γ σ' c (.base .bool)

/-- Loop-body boundary replay after a body-normal step, coarse compatibility surface. -/
structure LoopBodyAfterNormalCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  body_after_normal :
    ∀ {σ σ' : State},
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .normal σ' →
      LoopBodyBoundaryCI Γ σ' body

/-- Condition replay after a body-continue step. -/
structure LoopCondAfterContinueCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  cond_after_continue :
    ∀ {σ σ' : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .continueResult σ' →
      ExprReadyConcrete Γ σ' c (.base .bool)

/-- Loop-body boundary replay after a body-continue step, coarse compatibility surface. -/
structure LoopBodyAfterContinueCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  body_after_continue :
    ∀ {σ σ' : State},
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyBoundaryCI Γ σ' body

/--
Same-profile loop-body replay after a body-normal step.

The static parts are deliberately not returned.  The post-state boundary built
from this component must reuse:

- `hbody.structural`;
- `hbody.profile`.

Only the post-state dynamic boundary and same-profile post-state adequacy are
real obligations.
-/
structure LoopBodyAfterNormalSameProfileCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  dynamic_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      LoopBodyDynamicBoundary Γ σ' body

  adequacy_after_normal :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .normal σ' →
      LoopBodyAdequacyCI Γ σ' body hbody.profile

/--
Same-profile loop-body replay after a body-continue step.

This is the continue analogue of `LoopBodyAfterNormalSameProfileCI`.
-/
structure LoopBodyAfterContinueSameProfileCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  dynamic_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyDynamicBoundary Γ σ' body

  adequacy_after_continue :
    ∀ {σ σ' : State},
      (hbody : LoopBodyBoundaryCI Γ σ body) →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyAdequacyCI Γ σ' body hbody.profile

/--
Forget same-profile normal replay to the existing coarse normal replay surface.

The resulting boundary has the same structural/profile fields as the input
boundary by construction.
-/
def loopBodyAfterNormalCI_of_sameProfile
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (H : LoopBodyAfterNormalSameProfileCI Γ c body) :
    LoopBodyAfterNormalCI Γ c body :=
  { body_after_normal := by
      intro σ σ' hbody hstep
      exact
        { structural := hbody.structural
          profile := hbody.profile
          dynamic := H.dynamic_after_normal hbody hstep
          adequacy := H.adequacy_after_normal hbody hstep } }

/--
Forget same-profile continue replay to the existing coarse continue replay
surface.

The resulting boundary has the same structural/profile fields as the input
boundary by construction.
-/
def loopBodyAfterContinueCI_of_sameProfile
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (H : LoopBodyAfterContinueSameProfileCI Γ c body) :
    LoopBodyAfterContinueCI Γ c body :=
  { body_after_continue := by
      intro σ σ' hbody hstep
      exact
        { structural := hbody.structural
          profile := hbody.profile
          dynamic := H.dynamic_after_continue hbody hstep
          adequacy := H.adequacy_after_continue hbody hstep } }

/--
The same-profile normal replay wrapper really reuses the input structural field.
-/
theorem loopBodyAfterNormalCI_of_sameProfile_structural_eq
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (H : LoopBodyAfterNormalSameProfileCI Γ c body)
    {σ σ' : State}
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    ((loopBodyAfterNormalCI_of_sameProfile H).body_after_normal hbody hstep).structural =
      hbody.structural := by
  rfl

/--
The same-profile normal replay wrapper really reuses the input profile field.
-/
theorem loopBodyAfterNormalCI_of_sameProfile_profile_eq
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (H : LoopBodyAfterNormalSameProfileCI Γ c body)
    {σ σ' : State}
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .normal σ') :
    ((loopBodyAfterNormalCI_of_sameProfile H).body_after_normal hbody hstep).profile =
      hbody.profile := by
  rfl

/--
The same-profile continue replay wrapper really reuses the input structural field.
-/
theorem loopBodyAfterContinueCI_of_sameProfile_structural_eq
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (H : LoopBodyAfterContinueSameProfileCI Γ c body)
    {σ σ' : State}
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    ((loopBodyAfterContinueCI_of_sameProfile H).body_after_continue hbody hstep).structural =
      hbody.structural := by
  rfl

/--
The same-profile continue replay wrapper really reuses the input profile field.
-/
theorem loopBodyAfterContinueCI_of_sameProfile_profile_eq
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (H : LoopBodyAfterContinueSameProfileCI Γ c body)
    {σ σ' : State}
    (hbody : LoopBodyBoundaryCI Γ σ body)
    (hstep : BigStepStmt σ body .continueResult σ') :
    ((loopBodyAfterContinueCI_of_sameProfile H).body_after_continue hbody hstep).profile =
      hbody.profile := by
  rfl

/-- Reassemble the canonical `LoopReentryKernelCI` from header plus four coarse replay components. -/
def loopReentryKernelCI_of_components
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hheader : LoopReentryHeaderCI Γ c)
    (hcondNormal : LoopCondAfterNormalCI Γ c body)
    (hbodyNormal : LoopBodyAfterNormalCI Γ c body)
    (hcondContinue : LoopCondAfterContinueCI Γ c body)
    (hbodyContinue : LoopBodyAfterContinueCI Γ c body) :
    LoopReentryKernelCI Γ c body :=
  { hc := hheader.hc
    cond_after_normal := hcondNormal.cond_after_normal
    cond_after_continue := hcondContinue.cond_after_continue
    body_after_normal := hbodyNormal.body_after_normal
    body_after_continue := hbodyContinue.body_after_continue }

/--
Reassemble the canonical `LoopReentryKernelCI` from header, condition replay,
and same-profile body replay components.
-/
def loopReentryKernelCI_of_sameProfile_components
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hheader : LoopReentryHeaderCI Γ c)
    (hcondNormal : LoopCondAfterNormalCI Γ c body)
    (hbodyNormal : LoopBodyAfterNormalSameProfileCI Γ c body)
    (hcondContinue : LoopCondAfterContinueCI Γ c body)
    (hbodyContinue : LoopBodyAfterContinueSameProfileCI Γ c body) :
    LoopReentryKernelCI Γ c body :=
  loopReentryKernelCI_of_components
    hheader
    hcondNormal
    (loopBodyAfterNormalCI_of_sameProfile hbodyNormal)
    hcondContinue
    (loopBodyAfterContinueCI_of_sameProfile hbodyContinue)

/-- Project the static header component out of a `LoopReentryKernelCI`. -/
def loopReentryHeaderCI_of_kernel
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body) :
    LoopReentryHeaderCI Γ c :=
  { hc := K.hc }

/-- Project condition replay after normal out of a `LoopReentryKernelCI`. -/
def loopCondAfterNormalCI_of_kernel
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body) :
    LoopCondAfterNormalCI Γ c body :=
  { cond_after_normal := K.cond_after_normal }

/-- Project body-boundary replay after normal out of a `LoopReentryKernelCI`.

This is only the coarse compatibility projection.  It does not imply
same-profile replay.
-/
def loopBodyAfterNormalCI_of_kernel
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body) :
    LoopBodyAfterNormalCI Γ c body :=
  { body_after_normal := K.body_after_normal }

/-- Project condition replay after continue out of a `LoopReentryKernelCI`. -/
def loopCondAfterContinueCI_of_kernel
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body) :
    LoopCondAfterContinueCI Γ c body :=
  { cond_after_continue := K.cond_after_continue }

/-- Project body-boundary replay after continue out of a `LoopReentryKernelCI`.

This is only the coarse compatibility projection.  It does not imply
same-profile replay.
-/
def loopBodyAfterContinueCI_of_kernel
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body) :
    LoopBodyAfterContinueCI Γ c body :=
  { body_after_continue := K.body_after_continue }

/-- Eta sanity check for the component split of `LoopReentryKernelCI`. -/
theorem loopReentryKernelCI_eta_components
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body) :
    loopReentryKernelCI_of_components
      (loopReentryHeaderCI_of_kernel K)
      (loopCondAfterNormalCI_of_kernel K)
      (loopBodyAfterNormalCI_of_kernel K)
      (loopCondAfterContinueCI_of_kernel K)
      (loopBodyAfterContinueCI_of_kernel K) = K := by
  cases K
  rfl

/-- Current residual static header component, projected from the current reentry shell. -/
noncomputable def whileTailReentryHeaderCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopReentryHeaderCI Γ c :=
  loopReentryHeaderCI_of_kernel
    (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)

/-- Current residual condition replay after body-normal, projected from the current reentry shell. -/
noncomputable def whileTailCondAfterNormalCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopCondAfterNormalCI Γ c body :=
  loopCondAfterNormalCI_of_kernel
    (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)

/-- Current residual body-boundary replay after body-normal, projected from the current reentry shell.

This remains coarse: the current lower-level residual shell has not yet been
strengthened to same-profile replay.
-/
noncomputable def whileTailBodyAfterNormalCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopBodyAfterNormalCI Γ c body :=
  loopBodyAfterNormalCI_of_kernel
    (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)

/-- Current residual condition replay after body-continue, projected from the current reentry shell. -/
noncomputable def whileTailCondAfterContinueCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopCondAfterContinueCI Γ c body :=
  loopCondAfterContinueCI_of_kernel
    (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)

/-- Current residual body-boundary replay after body-continue, projected from the current reentry shell.

This remains coarse: the current lower-level residual shell has not yet been
strengthened to same-profile replay.
-/
noncomputable def whileTailBodyAfterContinueCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopBodyAfterContinueCI Γ c body :=
  loopBodyAfterContinueCI_of_kernel
    (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)

/-- Eta sanity check for the current residual reentry kernel through named coarse components. -/
theorem whileTailReentryKernelCI_of_bodyClosureBoundaryCI_eta_components
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    loopReentryKernelCI_of_components
      (whileTailReentryHeaderCI_of_bodyClosureBoundaryCI hentry)
      (whileTailCondAfterNormalCI_of_bodyClosureBoundaryCI hentry)
      (whileTailBodyAfterNormalCI_of_bodyClosureBoundaryCI hentry)
      (whileTailCondAfterContinueCI_of_bodyClosureBoundaryCI hentry)
      (whileTailBodyAfterContinueCI_of_bodyClosureBoundaryCI hentry) =
    whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry := by
  simpa
    [ whileTailReentryHeaderCI_of_bodyClosureBoundaryCI
    , whileTailCondAfterNormalCI_of_bodyClosureBoundaryCI
    , whileTailBodyAfterNormalCI_of_bodyClosureBoundaryCI
    , whileTailCondAfterContinueCI_of_bodyClosureBoundaryCI
    , whileTailBodyAfterContinueCI_of_bodyClosureBoundaryCI ]
    using
      loopReentryKernelCI_eta_components
        (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)

/--
Current-boundary while closure through header + four coarse reentry components
plus the already theorem-backed post-state adequacy components.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitReentryComponents
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hheader : LoopReentryHeaderCI Γ c)
    (hcondNormal : LoopCondAfterNormalCI Γ c body)
    (hbodyNormal : LoopBodyAfterNormalCI Γ c body)
    (hcondContinue : LoopCondAfterContinueCI Γ c body)
    (hbodyContinue : LoopBodyAfterContinueCI Γ c body)
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
    while_function_body_closure_boundary_ci_of_currentBoundary_splitPostAdequacy
      hentry
      (loopReentryKernelCI_of_components
        hheader hcondNormal hbodyNormal hcondContinue hbodyContinue)
      hnormal
      hcontinue
      htailClosure

/--
Current-boundary while closure through header + condition replay + same-profile
body replay components.

This is the preferred strengthened surface: body reentry now guarantees by type
that the replayed loop-body boundary reuses the original structural/profile
data.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitSameProfileReentryComponents
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hheader : LoopReentryHeaderCI Γ c)
    (hcondNormal : LoopCondAfterNormalCI Γ c body)
    (hbodyNormal : LoopBodyAfterNormalSameProfileCI Γ c body)
    (hcondContinue : LoopCondAfterContinueCI Γ c body)
    (hbodyContinue : LoopBodyAfterContinueSameProfileCI Γ c body)
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
    while_function_body_closure_boundary_ci_of_currentBoundary_splitPostAdequacy
      hentry
      (loopReentryKernelCI_of_sameProfile_components
        hheader hcondNormal hbodyNormal hcondContinue hbodyContinue)
      hnormal
      hcontinue
      htailClosure

/--
Current-boundary while closure through the current named coarse reentry
components.

The normal/continue tail adequacy arguments are now theorem-backed; the only
remaining current residuals in this route are the four reentry replay
components.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_currentReentryComponents
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
    while_function_body_closure_boundary_ci_of_currentBoundary_splitReentryComponents
      hentry
      (whileTailReentryHeaderCI_of_bodyClosureBoundaryCI hentry)
      (whileTailCondAfterNormalCI_of_bodyClosureBoundaryCI hentry)
      (whileTailBodyAfterNormalCI_of_bodyClosureBoundaryCI hentry)
      (whileTailCondAfterContinueCI_of_bodyClosureBoundaryCI hentry)
      (whileTailBodyAfterContinueCI_of_bodyClosureBoundaryCI hentry)
      (whileTailNormalAdequacyCI_of_bodyClosureBoundaryCI hentry)
      (whileTailContinueAdequacyCI_of_bodyClosureBoundaryCI hentry)
      htailClosure

end Cpp
