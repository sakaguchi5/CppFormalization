import CppFormalization.Cpp2.Metatheory.Closure.FunctionBodyCaseDriverCI
import CppFormalization.Cpp2.Metatheory.Closure.WhileCurrentBoundaryClosureCoreSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverCoreSupportCI

Case-driver body with `seq` and `while` both entering through clean support
objects.

Compared with `FunctionBodyCaseDriverProviderCI`, this layer removes the need for
`StmtNormalPreservationProviderCI.toWhileReentryReadyProvider` at the driver
surface.  The driver receives:

- `P : StmtNormalPreservationCoreCI`, the pure normal-preservation service;
- `Wh : WhileCurrentBoundaryClosureCoreSupportCI`, implementation support for while;
- `W : FunctionBodyWhileBackedgeInvariantCoreProviderCI`, the program-facing
  while backedge invariant provider.

Any old while-reentry implementation is now pushed into construction of `Seq`
and `Wh`, not into the case driver itself.
-/

/-- Provider for the program-facing while backedge invariant used by the driver. -/
structure FunctionBodyWhileBackedgeInvariantCoreProviderCI : Type where
  invariant :
    ∀ {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt},
      CoreBigStepFragment (.whileStmt c body) →
      BodyClosureBoundaryCI Γ σ (.whileStmt c body) →
      WhileBackedgeInvariantCI Γ c body

/-- Build the tail-closure shell from the case-driver recursive hypothesis. -/
def whileTailClosureShellCI_of_caseDriverIH_core
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body)) :
    WhileTailClosureShellCI Γ c body :=
  { close := by
      intro σ1 htailBoundary
      exact IH (st := .whileStmt c body) hfrag htailBoundary }

/-- The while branch through the clean closure-step support. -/
theorem while_case_driver_branch_of_coreSupport
    (Wh : WhileCurrentBoundaryClosureCoreSupportCI)
    (W : FunctionBodyWhileBackedgeInvariantCoreProviderCI)
    (IH : FunctionBodyCaseDriverIH)
    {Γ : TypeEnv} {σ : State} {c : ValExpr} {body : CppStmt}
    (hfrag : CoreBigStepFragment (.whileStmt c body))
    (hentry : BodyClosureBoundaryCI Γ σ (.whileStmt c body)) :
    FunctionBodyCaseDriverResult σ (.whileStmt c body) := by
  exact
    Wh.close
      hentry
      { invariant := W.invariant hfrag hentry
        tail := whileTailClosureShellCI_of_caseDriverIH_core IH hfrag }


end Cpp
