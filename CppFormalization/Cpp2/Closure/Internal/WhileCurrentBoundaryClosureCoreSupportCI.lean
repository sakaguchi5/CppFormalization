import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryClosureStepCI

namespace Cpp

/-!
# Closure.Internal.WhileCurrentBoundaryClosureCoreSupportCI

Pure caller-facing support for the current-boundary `while` closure step.

The cleaned while theorem still has an implementation parameter
`WhileReentryReadyProvider`.  This file hides that implementation detail behind a
closure support object.  The case driver can then talk about the already-clean
closure step surface instead of carrying while reentry as a global argument.
-/

/--
Support for closing one current-boundary while step.

This is proof architecture, not a program invariant.  The program-facing part is
still `WhileBackedgeInvariantCI`, stored inside `WhileCurrentBoundaryClosureStepCI`.
-/
structure WhileCurrentBoundaryClosureCoreSupportCI : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt},
      BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
      WhileCurrentBoundaryClosureStepCI Γ c body →
      (∃ ex σ', BigStepFunctionBody σ (.whileStmt c body) ex σ') ∨
        BigStepStmtDiv σ (.whileStmt c body)

/-- Build the current implementation support from a while-reentry provider. -/
def whileCurrentBoundaryClosureCoreSupportCI_of_whileReentry
    (mkWhileReentry : WhileReentryReadyProvider) :
    WhileCurrentBoundaryClosureCoreSupportCI :=
  { close := by
      intro Γ σ c body hentry S
      exact
        while_function_body_closure_boundary_ci_of_currentBoundary_closureStep
          mkWhileReentry hentry S }

end Cpp
