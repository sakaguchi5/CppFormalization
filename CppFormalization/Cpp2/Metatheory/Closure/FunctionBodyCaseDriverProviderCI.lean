import CppFormalization.Cpp2.Metatheory.Closure.FunctionBodyCaseDriverCI
import CppFormalization.Cpp2.Closure.Internal.WhileCurrentBoundaryClosureStepCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverProviderCI

Case-driver body with the `seq` branch depending on
`StmtNormalPreservationProviderCI` rather than directly on
`WhileReentryReadyProvider`.

The while branch is also routed through the cleaned current-boundary closure-step
surface.  It still uses the provider's compatibility projection to while reentry
because the current while theorem itself is built on `WhileReentryReadyProvider`.
-/

/-- Provider for the program-facing while backedge invariant used by the driver. -/
structure FunctionBodyWhileBackedgeInvariantProviderCI : Type where
  invariant :
    ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt},
      CoreBigStepFragment (.whileStmt c body) →
      BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
      WhileBackedgeInvariantCI Γ c body

/-- Build the tail-closure shell from the case-driver recursive hypothesis. -/
def whileTailClosureShellCI_of_caseDriverIH
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body)) :
    WhileTailClosureShellCI Γ c body :=
  { close := by
      intro σ1 htailBoundary
      exact IH (st := .whileStmt c body) hfrag htailBoundary }

/-- The while branch through the cleaned closure-step route. -/
theorem while_case_driver_branch_of_closureStep
    (W : FunctionBodyWhileBackedgeInvariantProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body))
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    FunctionBodyCaseDriverResult σ (.whileStmt c body) := by
  exact
    while_function_body_closure_boundary_ci_of_currentBoundary_closureStep
      hentry
      { invariant := W.invariant hfrag hentry
        tail := whileTailClosureShellCI_of_caseDriverIH IH hfrag }

end Cpp
