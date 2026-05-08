import CppFormalization.Cpp2.Closure.Internal.WhileBodyClassCI

namespace Cpp

/-!
# Closure.Internal.WhileTailReentryProviderSplitCI

Expose the two independent obligations hidden inside
`whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI`.

Important:
- `whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI` already exists in the
  current lower layer.  This file deliberately does not redeclare it.
- The only new named projection introduced here is the delimiter reentry
  component.
- The post-state tail adequacy component is referenced through the existing
  declaration.

This is a deliberately small transition layer.  It does not prove either
component yet; it makes the next theoremization target visible at the call site.
-/

/-- Reassemble a tail-boundary reentry provider from its two honest components. -/
def whileTailBoundaryReentryProviderCI_of_split
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hreentry : LoopReentryKernelCI Γ c body)
    (hadequacy : WhileTailAdequacyProviderCI Γ σ c body hentry.static) :
    WhileTailBoundaryReentryProviderCI hentry :=
  { reentry := hreentry
    tailAdequacy := hadequacy }

/-- The delimiter-reentry component of the current residual provider. -/
noncomputable def whileTailReentryKernelCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    LoopReentryKernelCI Γ c body :=
  (whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI hentry).reentry

/--
Eta sanity check for the residual provider using direct projections.

This intentionally uses direct field projections on the right-hand side.  A
similar statement through separately named component definitions is not
necessarily definitional, because one of those names may be an existing lower
layer declaration rather than a transparent projection introduced here.
-/
theorem whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI_eta_direct
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI hentry =
      whileTailBoundaryReentryProviderCI_of_split
        hentry
        (whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI hentry).reentry
        (whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI hentry).tailAdequacy := by
  cases whileTailBoundaryReentryProviderCI_of_bodyClosureBoundaryCI hentry
  rfl

/--
Current-boundary while closure through explicitly supplied split tail obligations.

This is the preferred local shape for the next phase: after the condition-first
while theorem, the remaining current-boundary debt is no longer a single opaque
provider.  It is precisely delimiter reentry plus post-state tail adequacy.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitProvider
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hreentry : LoopReentryKernelCI Γ c body)
    (hadequacy : WhileTailAdequacyProviderCI Γ σ c body hentry.static)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_reentryProvider
      hentry
      (whileTailBoundaryReentryProviderCI_of_split hentry hreentry hadequacy)
      htailClosure

/--
Current-boundary while closure through the two currently exposed residual
components.

The adequacy component uses the existing lower-layer declaration
`whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI`; this file only adds the
matching reentry projection and the split wrapper.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_splitComponents
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
    while_function_body_closure_boundary_ci_of_currentBoundary_splitProvider
      hentry
      (whileTailReentryKernelCI_of_bodyClosureBoundaryCI hentry)
      (whileTailAdequacyProviderCI_of_bodyClosureBoundaryCI hentry)
      htailClosure

end Cpp
