import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureCoreSupportCI

namespace Cpp

/-!
# Closure.Internal.SeqFunctionBodyClosureBoundaryCoreSupportCI

Boundary-only core support for route-aware sequence closure.

`SeqFunctionBodyClosureCoreSupportCI` contains both the boundary-level and
`BodyReadyCI` entry surfaces.  The constructor-level function-body case driver,
however, consumes only `BodyClosureBoundaryCI` entries; its ready wrapper enters
by first taking `hentry.toClosureBoundary`.

This file factors out the smaller dependency needed by that driver.  It is a
minor but useful surface cleanup: the case driver should not require the
ready-entry sequence theorem when it only uses the boundary-entry one.
-/

/--
Boundary-only support for route-aware sequence closure from a pure normal
preservation core.

C++ reading: to close a sequence at the function-body boundary, we only need the
left closure and the route-aware tail closure at the boundary level.  The
separate `BodyReadyCI` convenience surface is not part of the constructor-level
case driver dependency.
-/
structure SeqFunctionBodyClosureBoundaryCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  close :
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

/-- Forget full sequence core support to the boundary-only support. -/
def seqFunctionBodyClosureBoundaryCoreSupportCI_of_coreSupport
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqFunctionBodyClosureCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  { close := Seq.closeBoundary }

/-- Build boundary-only support from the current compatibility provider. -/
def seqFunctionBodyClosureBoundaryCoreSupportCI_of_normalPreservationProvider
    (P : StmtNormalPreservationProviderCI) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P.toCore :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_coreSupport
    (seqFunctionBodyClosureCoreSupportCI_of_normalPreservationProvider P)

/-- Compatibility bridge from the old while-reentry provider. -/
def seqFunctionBodyClosureBoundaryCoreSupportCI_of_whileReentry
    (mkWhileReentry : WhileReentryReadyProvider) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI
      (stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry).toCore :=
  seqFunctionBodyClosureBoundaryCoreSupportCI_of_normalPreservationProvider
    (stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry)

/--
Boundary closure through boundary-only core support.

This theorem is intentionally just a readable application wrapper; downstream
case-driver code should depend on the smaller boundary-only support object.
-/
theorem seq_function_body_closure_boundary_ci_of_boundaryCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqFunctionBodyClosureBoundaryCoreSupportCI P)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        BodyClosureBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) :=
  Seq.close hentry leftClosure tailClosure

end Cpp
