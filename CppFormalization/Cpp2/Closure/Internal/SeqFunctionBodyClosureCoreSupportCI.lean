import CppFormalization.Cpp2.Closure.Internal.SeqNormalPreservationCoreCI
import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureProviderCI

namespace Cpp

/-!
# Closure.Internal.SeqFunctionBodyClosureCoreSupportCI

Pure-core sequence closure support.

`StmtNormalPreservationCoreCI` is the dependency that `seq` genuinely needs:
normal preservation for the left statement before entering the tail.  Older
sequence theorems still bottom out in `WhileReentryReadyProvider`; this file
separates the clean *seq-facing* support from that compatibility implementation.

C++ reading: sequencing does not care about while reentry.  It only needs the
fact that after the left statement falls through normally, the post-state is
well-scoped/well-typed for the environment that types the right statement.
-/

/--
Pure support for route-aware sequence closure from a normal-preservation core.

This is deliberately indexed by `P : StmtNormalPreservationCoreCI`: the support
says that the route-aware sequence closure theorem has been implemented using
that core preservation service.  It contains both the closure-boundary and
`BodyReadyCI` entry surfaces.
-/
structure SeqFunctionBodyClosureCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  closeBoundary :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s) →
      (∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyClosureBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) →
      FunctionBodyClosureResult σ (.seq s t)

  closeReady :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyReadyCI Γ σ (.seq s t)) →
      (BodyReadyCI Γ σ s →
        FunctionBodyClosureResult σ s) →
      (∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry.toClosureBoundary).profile) →
        BodyReadyCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) →
      FunctionBodyClosureResult σ (.seq s t)

/--
Build pure-core sequence support from the current compatibility provider.

This is the bridge for the current implementation.  The clean caller-facing
object is `SeqFunctionBodyClosureCoreSupportCI P.toCore`; the old
`WhileReentryReadyProvider` appears only in the implementation provider used to
construct that support.
-/
def seqFunctionBodyClosureCoreSupportCI_of_normalPreservationProvider
    (P : StmtNormalPreservationProviderCI) :
    SeqFunctionBodyClosureCoreSupportCI P.toCore :=
  { closeBoundary := by
      intro Γ σ s t hentry leftClosure tailClosure
      exact
        seq_function_body_closure_boundary_ci_honest_of_normalPreservationProvider
          P hentry leftClosure tailClosure
    closeReady := by
      intro Γ σ s t hentry leftClosure tailClosure
      exact
        seq_function_body_closure_ci_honest_of_normalPreservationProvider
          P hentry leftClosure tailClosure }

/-- Compatibility bridge from the old while-reentry provider. -/
def seqFunctionBodyClosureCoreSupportCI_of_whileReentry:
    SeqFunctionBodyClosureCoreSupportCI
      (stmtNormalPreservationProviderCI_of_whileReentry ).toCore :=
  seqFunctionBodyClosureCoreSupportCI_of_normalPreservationProvider
    (stmtNormalPreservationProviderCI_of_whileReentry )

end Cpp
