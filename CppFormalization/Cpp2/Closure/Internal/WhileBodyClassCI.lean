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
- additionally expose a reentry-based route where tail-boundary reconstruction
  is assembled from `LoopReentryKernelCI` plus a post-state adequacy provider.
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

This is the surface that should replace direct uses of
`whileTailBoundaryKitCI_of_bodyClosureBoundaryCI` when proving concrete classes.
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
The class object consumed by the while case kernel.

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

/-- Forget the entry component and keep exactly the class payload consumed by the kernel. -/
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

This is the key connection from `LoopReentryKernelCI` to the tail-boundary kit.
It does not hide the remaining adequacy obligation.
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

/-- The theorem-backed while typing exposed by the current-entry component. -/
theorem whileTyping
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)}
    (S : WhileBodyReentrySupportCI hentry) :
    HasTypeStmtCI .normalK Γ (.whileStmt c body) Γ :=
  S.toComponents.whileTyping

/-- Local body progress/divergence through the loop-boundary component. -/
theorem bodyProgressOrDiverges
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    {hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)}
    (S : WhileBodyReentrySupportCI hentry) :
    (∃ ctrl σ1, BigStepStmt σ body ctrl σ1) ∨ BigStepStmtDiv σ body :=
  S.toClass.bodyProgressOrDiverges

end WhileBodyReentrySupportCI

/--
Build the decomposed while-local components from a top-level while boundary.

This is no longer a single opaque class axiom:
- `entry` is theorem-backed;
- `loopBoundary` is provided by the remaining loop-body obligation;
- `tailBoundary` is provided by the remaining delimiter/reentry obligation.
-/
noncomputable def whileBodyClassComponentsCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    WhileBodyClassComponentsCI Γ σ c body :=
  { entry := whileEntryBoundaryCI_of_bodyClosureBoundaryCI hentry
    loopBoundary := whileLoopBoundaryCI_of_bodyClosureBoundaryCI hentry
    tailBoundary := whileTailBoundaryKitCI_of_bodyClosureBoundaryCI hentry }

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
Class extracted from a top-level `while` closure boundary.

This is retained for callers, but it is now just a projection from the
decomposed components above, not an independent axiom.
-/
noncomputable def whileBodyClassCI_of_bodyClosureBoundaryCI
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt} :
    BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
    WhileBodyClassCI Γ σ c body := by
  intro hentry
  exact (whileBodyClassComponentsCI_of_bodyClosureBoundaryCI hentry).toClass

/--
Class-based wrapper around the honest while kernel.

The typing premise can now be supplied by
`whileTypingCI_of_bodyClosureBoundaryCI`, and the class itself is only the
pair of remaining local-body / tail-reentry supports.
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

This is the preferred route for new code because it keeps the theorem-backed
current-entry facts visible and separates the two remaining obligations.
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
Reentry-support wrapper.

This is the preferred route once a concrete proof supplies a
`LoopReentryKernelCI` and the remaining post-state adequacy provider.
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
    while_function_body_closure_boundary_ci_of_components
      hentry
      S.toComponents
      htailClosure

end Cpp
