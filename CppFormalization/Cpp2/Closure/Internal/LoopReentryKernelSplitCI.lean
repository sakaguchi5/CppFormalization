import CppFormalization.Cpp2.Closure.Internal.WhileTailAdequacyProviderSplitCI

namespace Cpp

/-!
# Closure.Internal.LoopReentryKernelSplitCI

Expose the dynamic reentry obligations inside `LoopReentryKernelCI`.

The previous split established that normal/continue post-state tail adequacy is
theorem-backed from the original top-level while adequacy.  The remaining while
debt is now the delimiter reentry/dynamic reconstruction side.

This file keeps `LoopReentryKernelCI` as the canonical kernel, but exposes its
parts as named components:

- `LoopReentryHeaderCI`: static header typing for the condition;
- `LoopCondAfterNormalCI`: condition replay after a body-normal step;
- `LoopBodyAfterNormalCI`: loop-body boundary replay after a body-normal step;
- `LoopCondAfterContinueCI`: condition replay after a body-continue step;
- `LoopBodyAfterContinueCI`: loop-body boundary replay after a body-continue step.

The four replay components are the actual dynamic/invariant obligations.  The
header component is separated because it is static typing data, not a reentry
invariant.
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

/-- Loop-body boundary replay after a body-normal step. -/
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

/-- Loop-body boundary replay after a body-continue step. -/
structure LoopBodyAfterContinueCI
    (Γ : TypeEnv) (_c : ValExpr) (body : CppStmt) : Type where
  body_after_continue :
    ∀ {σ σ' : State},
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .continueResult σ' →
      LoopBodyBoundaryCI Γ σ' body

/-- Reassemble the canonical `LoopReentryKernelCI` from header plus four replay components. -/
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

/-- Project body-boundary replay after normal out of a `LoopReentryKernelCI`. -/
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

/-- Project body-boundary replay after continue out of a `LoopReentryKernelCI`. -/
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

/-- Current residual body-boundary replay after body-normal, projected from the current reentry shell. -/
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

/-- Current residual body-boundary replay after body-continue, projected from the current reentry shell. -/
noncomputable def whileTailBodyAfterContinueCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopBodyAfterContinueCI Γ c body :=
  loopBodyAfterContinueCI_of_kernel
    (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)

/-- Eta sanity check for the current residual reentry kernel through named components. -/
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
Current-boundary while closure through header + four reentry components plus
the already theorem-backed post-state adequacy components.
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
Current-boundary while closure through the current named reentry components.

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
