import CppFormalization.Cpp2.Closure.Internal.FunctionBodyCaseDriverContinuationSeqSupportCI

namespace Cpp

/-!
# Closure.Internal.FunctionBodyCaseDriverContinuationIHCI

Continuation-boundary recursive hypothesis for the function-body case driver.

The previous driver IH consumes `BodyClosureBoundaryCI`.  That is still usable,
but it keeps the recursion interface tied to the old closure-boundary surface.

This file introduces the next surface:

`FunctionBodyContinuationCaseDriverIH`

which consumes `StmtContinuationBoundaryCI`.  During the transition, this IH can
be forgotten back to the old `FunctionBodyCaseDriverIH` by converting a
`BodyClosureBoundaryCI` into a continuation boundary.  The important design
move is that new call sites can now state the recursive demand in terms of
post-state continuation boundaries.
-/

/-- Recursive hypothesis whose entry boundary is the full statement continuation
boundary. -/
abbrev FunctionBodyContinuationCaseDriverIH : Prop :=
  ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
    CoreBigStepFragment st →
    StmtContinuationBoundaryCI Γ σ st →
    FunctionBodyCaseDriverResult σ st

namespace FunctionBodyContinuationCaseDriverIH

/-- Forget a continuation-boundary IH to the old closure-boundary IH.

This is the transitional adapter.  It should eventually become unnecessary once
the constructor-level driver directly consumes continuation boundaries in every
branch.
-/
def toBoundaryIH
    (IH : FunctionBodyContinuationCaseDriverIH) :
    FunctionBodyCaseDriverIH :=
  fun {Γ σ st} hfrag hentry =>
    IH (Γ := Γ) (σ := σ) (st := st) hfrag
      (StmtContinuationBoundaryCI.ofBodyClosureBoundaryCI hentry)

end FunctionBodyContinuationCaseDriverIH






end Cpp
