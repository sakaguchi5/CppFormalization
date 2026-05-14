import CppFormalization.Cpp2.Static.Safety.ReadinessSemanticsBridge
import CppFormalization.Cpp2.Closure.Internal.WhileFunctionClosureKernelCI

namespace Cpp

/-!
# Closure.Internal.SmallReusableWrappersCI

Small derived assets used by later closure proofs.
-/

/--
A ready expression can be evaluated, and its value is compatible with its static
type.  This packages the two existing facts `expr_ready_to_bigstep` and
`expr_ready_eval_compat`.
-/
structure ExprReadyEvaluationPackage
    (Γ : TypeEnv) (σ : State) (e : ValExpr) (τ : CppType) : Type where
  v : Value
  step : BigStepValue σ e v
  compat : ValueCompat v τ

namespace ExprReadyConcrete

noncomputable def exprReadyBigStepWitness
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
    (h : ExprReadyConcrete Γ σ e τ) :
    { v : Value // BigStepValue σ e v } :=
  let hex : ∃ v, BigStepValue σ e v := expr_ready_to_bigstep h
  ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- Package expression evaluation and compatibility from readiness. -/
noncomputable def toEvaluationPackage
    {Γ : TypeEnv} {σ : State} {e : ValExpr} {τ : CppType}
    (h : ExprReadyConcrete Γ σ e τ) :
    ExprReadyEvaluationPackage Γ σ e τ :=
  let w := exprReadyBigStepWitness h
  { v := w.val
    step := w.property
    compat := expr_ready_eval_compat h w.property }

end ExprReadyConcrete

/--
The dynamic part of a tail `while` boundary after a normal or continue body
step.

This separates the dynamic provider produced by `LoopReentryKernelCI` from the
post-state adequacy provider needed for the full tail boundary.
-/
structure WhileTailDynamicProviderCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  afterNormal :
    ∀ {σ1 : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .normal σ1 →
      BodyDynamicBoundary Γ σ1 (.whileStmt c body)
  afterContinue :
    ∀ {σ1 : State},
      ExprReadyConcrete Γ σ c (.base .bool) →
      LoopBodyBoundaryCI Γ σ body →
      BigStepStmt σ body .continueResult σ1 →
      BodyDynamicBoundary Γ σ1 (.whileStmt c body)

namespace LoopReentryKernelCI

/-- Expose the dynamic-provider part of `LoopReentryKernelCI`. -/
def toWhileTailDynamicProvider
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (K : LoopReentryKernelCI Γ c body) :
    WhileTailDynamicProviderCI Γ σ c body :=
  { afterNormal := by
      intro σ1 hcond hbody hstep
      exact K.whileDynamic_after_normal hcond hbody hstep
    afterContinue := by
      intro σ1 hcond hbody hstep
      exact K.whileDynamic_after_continue hcond hbody hstep }

end LoopReentryKernelCI

/--
A convenience wrapper around the already honest tail-boundary constructor.

It reads the current `WhileEntryBoundaryCI` from the top-level while closure
boundary and keeps reentry-dynamic evidence separate from post-state adequacy.
-/
def whileTailBoundaryKitCI_of_entry_reentry_adequacy
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body)
    (hreentry : LoopReentryKernelCI Γ c body)
    (hadequacy : WhileTailAdequacyProviderCI Γ σ c body hentry.static) :
    WhileTailBoundaryKitCI Γ σ c body :=
  whileTailBoundaryKitCI_of_loopReentry
    hentry
    (whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry)
    hloop
    hreentry
    hadequacy

end Cpp
