import CppFormalization.Cpp2.Closure.Internal.WhileFunctionClosureKernelCI

namespace Cpp

/-!
# Closure.Internal.WhileBodyClassCI

`while` を theorem-backed にできる body class を明示するための internal vocabulary.

Redesign:
- do not treat `whileBodyClassCI_of_bodyClosureBoundaryCI` as a primitive shell;
- decompose it into:
  1. current-entry facts, theorem-backed by `WhileEntryBoundaryCI`;
  2. loop-body local boundary, still a real local-body obligation;
  3. tail-boundary reconstruction, still a real delimiter/reentry obligation.
- expose a reentry-provider route where the mainline closure theorem follows the
  C++ condition-first execution order and avoids the older compatibility kits.

2026-05 patch note:
- The old direct extraction wrappers
  `whileBodyClassComponentsCI_of_bodyClosureBoundaryCI` and
  `whileBodyClassCI_of_bodyClosureBoundaryCI` are now kept only as a commented
  legacy block below.  They route through the unconditional current-boundary
  loop-body extraction, which is too strong as a canonical C++ story: a body
  return can be exposed through the whole `while` only after the condition has
  actually evaluated to `true`.
- The preferred public route is now the reentry-provider route:
  `whileBodyReentrySupportCI_of_bodyClosureBoundaryCI` plus
  `while_function_body_closure_boundary_ci_of_reentrySupport`, or directly
  `while_function_body_closure_boundary_ci_of_currentBoundary_reentryProvider`.
-/

/--
The decomposed while-local support visible at a top-level `while` entry.

`entry` is theorem-backed from the top-level boundary.
`loopBoundary` and `tailBoundary` remain the two genuine obligations.
-/
structure WhileBodyClassComponentsCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  entry :
    WhileEntryBoundaryCI Γ σ c body
  loopBoundary :
    LoopBodyBoundaryCI Γ σ body
  tailBoundary :
    WhileTailBoundaryKitCI Γ σ c body

/--
A more honest reentry-based while-local support package.

It replaces an opaque tail-boundary kit by:
- current entry,
- loop-body local boundary,
- delimiter reentry kernel,
- the remaining post-state top-level while adequacy provider.

The clean closure wrapper below converts this object to a
`WhileTailBoundaryReentryProviderCI` and calls the condition-first while theorem.
-/
structure WhileBodyReentrySupportCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) : Type where
  currentEntry :
    WhileEntryBoundaryCI Γ σ c body
  loopBoundary :
    LoopBodyBoundaryCI Γ σ body
  reentry :
    LoopReentryKernelCI Γ c body
  tailAdequacy :
    WhileTailAdequacyProviderCI Γ σ c body hentry.static

/--
The class object consumed by the older kit-based wrapper.

It intentionally contains only the two operational supports needed by the
honest while theorem.  The current-entry data is kept in
`WhileBodyClassComponentsCI`, not duplicated here.
-/
structure WhileBodyClassCI
    (Γ : TypeEnv) (σ : State) (c : ValExpr) (body : CppStmt) : Type where
  loopBoundary :
    LoopBodyBoundaryCI Γ σ body
  tailBoundary :
    WhileTailBoundaryKitCI Γ σ c body

namespace WhileBodyClassCI

/--
Local body progress/divergence is derived from the class boundary itself.
-/
theorem bodyProgressOrDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (K : WhileBodyClassCI Γ σ c body) :
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body :=
  loop_body_function_progress_or_diverges_ci K.loopBoundary

end WhileBodyClassCI

namespace WhileBodyClassComponentsCI

/-- Forget the entry component and keep exactly the class payload consumed by the kit-based wrapper. -/
def toClass
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (K : WhileBodyClassComponentsCI Γ σ c body) :
    WhileBodyClassCI Γ σ c body :=
  { loopBoundary := K.loopBoundary
    tailBoundary := K.tailBoundary }

/-- The theorem-backed while typing exposed by the current-entry component. -/
theorem whileTyping
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (K : WhileBodyClassComponentsCI Γ σ c body) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ :=
  whileTypingCI_of_whileEntryBoundaryCI K.entry

/-- Local body progress/divergence through the loop-boundary component. -/
theorem bodyProgressOrDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (K : WhileBodyClassComponentsCI Γ σ c body) :
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body :=
  K.toClass.bodyProgressOrDiverges

end WhileBodyClassComponentsCI

namespace WhileBodyReentrySupportCI

/--
Assemble the ordinary component package from reentry support.

This compatibility projection is still useful for callers that explicitly want a
`WhileBodyClassComponentsCI`, but the preferred closure theorem below does not
need to build a tail-boundary kit eagerly.
-/
def toComponents
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)}
    (S : WhileBodyReentrySupportCI hentry) :
    WhileBodyClassComponentsCI Γ σ c body :=
  { entry := S.currentEntry
    loopBoundary := S.loopBoundary
    tailBoundary :=
      whileTailBoundaryKitCI_of_loopReentry
        hentry
        S.currentEntry
        S.loopBoundary
        S.reentry
        S.tailAdequacy }

/-- The class payload induced by reentry support. -/
def toClass
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)}
    (S : WhileBodyReentrySupportCI hentry) :
    WhileBodyClassCI Γ σ c body :=
  S.toComponents.toClass

/--
Forget only to the smaller tail-boundary reentry provider.

This is the preferred forgetful map for the condition-first route: it preserves
exactly the two genuine tail obligations and avoids constructing a
`WhileTailBoundaryKitCI` before the condition is evaluated.
-/
def toTailBoundaryReentryProvider
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)}
    (S : WhileBodyReentrySupportCI hentry) :
    WhileTailBoundaryReentryProviderCI hentry :=
  { reentry := S.reentry
    tailAdequacy := S.tailAdequacy }

/-- The theorem-backed while typing exposed by the current-entry component. -/
theorem whileTyping
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)}
    (S : WhileBodyReentrySupportCI hentry) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ :=
  whileTypingCI_of_whileEntryBoundaryCI S.currentEntry

/-- Local body progress/divergence through the loop-boundary component. -/
theorem bodyProgressOrDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)}
    (S : WhileBodyReentrySupportCI hentry) :
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body :=
  S.toClass.bodyProgressOrDiverges

end WhileBodyReentrySupportCI

/--
Build the reentry-based while-local support from explicit obligations.

This is the preferred theorem-proving route for concrete while-body classes.
-/
def whileBodyReentrySupportCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hloop : LoopBodyBoundaryCI Γ σ body)
    (hreentry : LoopReentryKernelCI Γ c body)
    (hadequacy : WhileTailAdequacyProviderCI Γ σ c body hentry.static) :
    WhileBodyReentrySupportCI hentry :=
  { currentEntry := whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry
    loopBoundary := hloop
    reentry := hreentry
    tailAdequacy := hadequacy }

/--
Class-based wrapper around the honest while kernel.

This compatibility wrapper consumes a prebuilt tail-boundary kit.
The newer reentry-provider wrapper below is the preferred mainline route.
-/
theorem while_function_body_closure_boundary_ci_of_class
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (htyWhile : HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ)
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (K : WhileBodyClassCI Γ σ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_honest
      htyWhile
      hentry
      K.loopBoundary
      K.bodyProgressOrDiverges
      K.tailBoundary
      htailClosure

/--
Component-based wrapper.

This is retained for compatibility with the older components surface.
-/
theorem while_function_body_closure_boundary_ci_of_components
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (K : WhileBodyClassComponentsCI Γ σ c body)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_class
      K.whileTyping
      hentry
      K.toClass
      htailClosure

/--
Condition-first wrapper from a current boundary and a reentry provider.

This is the clean mainline route: it avoids the old unconditional loop-body
return-exposure compatibility shell and avoids extracting a direct
`WhileTailBoundaryKitCI` from the current boundary.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_reentryProvider
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (P : WhileTailBoundaryReentryProviderCI hentry)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_reentryProvider_condition_first
      (whileTypingCI_of_bodyClosureBoundaryCI hentry)
      hentry
      P
      htailClosure

/--
Reentry-support wrapper.

This now uses the condition-first reentry-provider route directly, instead of
first constructing `WhileBodyClassComponentsCI` and a tail-boundary kit.
-/
theorem while_function_body_closure_boundary_ci_of_reentrySupport
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (S : WhileBodyReentrySupportCI hentry)
    (htailClosure :
      ∀ {σ1 : State},
        BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_reentryProvider_condition_first
      (WhileBodyReentrySupportCI.whileTyping S)
      hentry
      (WhileBodyReentrySupportCI.toTailBoundaryReentryProvider S)
      htailClosure

end Cpp
