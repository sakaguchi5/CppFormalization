import CppFormalization.Cpp3.Continuation.Core

/-!
# CppFormalization.Cpp3.Continuation.While

Continuation surfaces for selected while-boundary routes.

This file deliberately does not require termination.  A safe loop may diverge;
the continuation surface records how a selected while boundary exposes the next
runtime state and the boundary package available there.
-/

namespace Cpp3
namespace Continuation

/-- Continuation package for a selected while-boundary route. -/
structure WhileBoundaryContinuation
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  stability : Stability.WhileBoundaryStability Γ Γc σ cond body

namespace WhileBoundaryContinuation

/-- The source boundary for the whole while statement. -/
def source
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundaryContinuation Γ Γc σ cond body) :
    Boundary.StmtBoundary Γ σ (.whileStmt cond body) :=
  h.stability.source

/-- The target while boundary package. -/
def target
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundaryContinuation Γ Γc σ cond body) :
    Boundary.WhileBoundary Γ Γc σ cond body :=
  h.stability.target

/-- The state reached immediately after evaluating the guard. -/
def conditionPostState
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundaryContinuation Γ Γc σ cond body) : State :=
  Semantics.WhileBoundaryRoute.conditionPostState h.target.route

/-- The state reached by the selected one-step while boundary route. -/
def routePostState
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundaryContinuation Γ Γc σ cond body) : State :=
  h.stability.routePostState

end WhileBoundaryContinuation

/-- A reentry handoff for while routes that return to the loop guard.

The proposition is visible: later proof files should instantiate it with the
specific claim that the route is a normal/continue backedge rather than an exit,
break, or return route. -/
structure WhileReentryContinuation
    (Γ Γc : TypeEnv) (σ σreentry : State) (cond : CppCond) (body : CppStmt)
    (Reentry : Prop) : Type where
  boundary : WhileBoundaryContinuation Γ Γc σ cond body
  reentryEq : boundary.routePostState = σreentry
  reentryBoundary : Boundary.StmtBoundary Γ σreentry (.whileStmt cond body)
  certificate : ContinuationCertificate Reentry

end Continuation
end Cpp3
