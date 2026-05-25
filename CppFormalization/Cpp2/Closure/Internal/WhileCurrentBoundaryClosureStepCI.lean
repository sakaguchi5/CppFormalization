import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryBackedgeInvariantCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryClosureStepCI

Name the proof-architecture shell that remains after the current-boundary
`while` replay surface has been reduced to the genuine backedge invariant.

At the previous layer, the current-boundary theorem takes:

- the current `BodyClosureBoundaryCI` for the `while`;
- the program-facing `WhileBackedgeInvariantCI`;
- a tail-closure recursion assumption.

The first two are semantic/program-facing data.  The last one is not a C++ loop
invariant: it is the recursion/case-driver hook that closes the tail `while`
after one normal or continue backedge.

This file gives that hook a small explicit name and then offers a combined
closure-step support object for callers that want to pass the current while step
as one proof-architecture package.
-/

/--
The recursive tail-closure shell for a fixed `while (c) body`.

C++ reading: whenever a later iteration boundary is available, the surrounding
case-driver/recursor can close that tail `while` by producing either a function
body result or divergence.

This is deliberately not bundled into `WhileBackedgeInvariantCI`, because it is
proof architecture rather than a program-facing loop invariant.
-/
structure WhileTailClosureShellCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  close :
    ∀ {σ1 : State},
      BodyClosureBoundaryCI Γ σ1 (.whileStmt c body) →
        (∃ ex σ2, BigStepFunctionBody σ1 (.whileStmt c body) ex σ2) ∨
          BigStepStmtDiv σ1 (.whileStmt c body)

/--
A named support package for one current-boundary `while` closure step.

It intentionally separates the program-facing backedge invariant from the
recursion shell:

- `invariant` is the C++/semantic backedge condition;
- `tail` is the proof-architecture recursion hook.
-/
structure WhileCurrentBoundaryClosureStepCI
    (Γ : TypeEnv) (c : ValExpr) (body : CppStmt) : Type where
  invariant : WhileBackedgeInvariantCI Γ c body
  tail : WhileTailClosureShellCI Γ c body

/-- Project the program-facing invariant from the closure-step support. -/
def whileBackedgeInvariantCI_of_closureStep
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryClosureStepCI Γ c body) :
    WhileBackedgeInvariantCI Γ c body :=
  S.invariant

/-- Project the recursion shell from the closure-step support. -/
def whileTailClosureShellCI_of_closureStep
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryClosureStepCI Γ c body) :
    WhileTailClosureShellCI Γ c body :=
  S.tail

/-- Reassemble closure-step support from its two explicit components. -/
def whileCurrentBoundaryClosureStepCI_of_components
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (I : WhileBackedgeInvariantCI Γ c body)
    (T : WhileTailClosureShellCI Γ c body) :
    WhileCurrentBoundaryClosureStepCI Γ c body :=
  { invariant := I
    tail := T }

/-- Eta sanity check for the closure-step support split. -/
theorem whileCurrentBoundaryClosureStepCI_eta_components
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (S : WhileCurrentBoundaryClosureStepCI Γ c body) :
    whileCurrentBoundaryClosureStepCI_of_components S.invariant S.tail = S := by
  cases S
  rfl

/--
Current-boundary while closure through a named tail-closure shell.

This is just the previous cleaned theorem with the raw recursion function named
as `WhileTailClosureShellCI`.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_backedgeInvariant_tailClosureShell
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (hinvariant : WhileBackedgeInvariantCI Γ c body)
    (htail : WhileTailClosureShellCI Γ c body) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_backedgeInvariant_tailAdequacyTheorems
      hentry
      hinvariant
      htail.close

/--
Current-boundary while closure through one named closure-step support object.

The current while boundary remains separate: it is the input boundary for this
particular state.  The support object contains the reusable route invariant plus
the tail-recursion hook.
-/
theorem while_function_body_closure_boundary_ci_of_currentBoundary_closureStep
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body))
    (S : WhileCurrentBoundaryClosureStepCI Γ c body) :
    (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
      BigStepStmtDiv σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_backedgeInvariant_tailClosureShell
      hentry
      S.invariant
      S.tail

end Cpp
