import CppFormalization.Cpp2.Closure.Internal.SeqFunctionBodyClosureBoundaryCoreSupportCI
import CppFormalization.Cpp2.Continuation.Boundary.Body

namespace Cpp

/-!
# Closure.Internal.SeqFunctionBodyClosureContinuationCoreSupportCI

Boundary-level seq closure support whose tail callback receives a full
post-route continuation boundary.

This is the next surface after `SeqFunctionBodyClosureBoundaryCoreSupportCI`:
the old surface says the selected tail is a `BodyClosureBoundaryCI`; this one
says it is a `StmtContinuationBoundaryCI`.

The two are currently inter-convertible because `StmtContinuationBoundaryCI`
is a full four-layer boundary wrapper.  The direction of travel is to make the
continuation surface canonical and eventually stop speaking about readiness
transport at this boundary.
-/

/-- Seq closure support with a continuation-boundary tail callback. -/
structure SeqFunctionBodyClosureContinuationCoreSupportCI
    (P : StmtNormalPreservationCoreCI) : Type where
  close :
    ∀ {Γ : TypeEnv} {σ : State} {s t : CppStmt},
      (hentry : BodyClosureBoundaryCI Γ σ (.seq s t)) →
      (BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s) →
      (∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) →
      FunctionBodyClosureResult σ (.seq s t)

namespace SeqFunctionBodyClosureContinuationCoreSupportCI

/-- Forget continuation-tail support to the older boundary-tail support. -/
def toBoundaryCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P) :
    SeqFunctionBodyClosureBoundaryCoreSupportCI P :=
  { close := fun hentry leftClosure tailClosure =>
      Seq.close
        hentry
        leftClosure
        (fun route htailContinuation =>
          tailClosure route htailContinuation.toBodyClosureBoundaryCI) }

/-- Build continuation-tail support from the older boundary-tail support.

This is the compatibility direction used during migration: the old selected
tail boundary is immediately re-presented as a continuation boundary.
-/
def ofBoundaryCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqFunctionBodyClosureBoundaryCoreSupportCI P) :
    SeqFunctionBodyClosureContinuationCoreSupportCI P :=
  { close := fun hentry leftClosure tailClosure =>
      Seq.close
        hentry
        leftClosure
        (fun route htailBoundary =>
          tailClosure route
            (StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI htailBoundary)) }

end SeqFunctionBodyClosureContinuationCoreSupportCI

/-- Build continuation-tail support from the current normal-preservation
provider surface. -/
def seqFunctionBodyClosureContinuationCoreSupportCI_of_normalPreservationProvider
    (P : StmtNormalPreservationProviderCI) :
    SeqFunctionBodyClosureContinuationCoreSupportCI P.toCore :=
  SeqFunctionBodyClosureContinuationCoreSupportCI.ofBoundaryCoreSupport
    (seqFunctionBodyClosureBoundaryCoreSupportCI_of_normalPreservationProvider P)

/-- Compatibility bridge from the old while-reentry provider. -/
def seqFunctionBodyClosureContinuationCoreSupportCI_of_whileReentry
    (mkWhileReentry : WhileReentryReadyProvider) :
    SeqFunctionBodyClosureContinuationCoreSupportCI
      (stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry).toCore :=
  seqFunctionBodyClosureContinuationCoreSupportCI_of_normalPreservationProvider
    (stmtNormalPreservationProviderCI_of_whileReentry mkWhileReentry)

/-- Readable application wrapper for continuation-tail support. -/
theorem seq_function_body_closure_boundary_ci_of_continuationCoreSupport
    {P : StmtNormalPreservationCoreCI}
    (Seq : SeqFunctionBodyClosureContinuationCoreSupportCI P)
    {Γ : TypeEnv} {σ : State} {s t : CppStmt}
    (hentry : BodyClosureBoundaryCI Γ σ (.seq s t))
    (leftClosure :
      BodyClosureBoundaryCI Γ σ s →
        FunctionBodyClosureResult σ s)
    (tailClosure :
      ∀ {σ1 : State},
        (route : SeqHeadNormalRouteCI Γ σ s t σ1
          (seq_left_static_boundary_ci_of_entry hentry).profile) →
        StmtContinuationBoundaryCI route.Θ σ1 t →
        FunctionBodyClosureResult σ1 t) :
    FunctionBodyClosureResult σ (.seq s t) :=
  Seq.close hentry leftClosure tailClosure

end Cpp
