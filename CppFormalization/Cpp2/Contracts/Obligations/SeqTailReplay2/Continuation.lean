import CppFormalization.Cpp2.Contracts.Obligations.SeqTailReplay2.Stmt

namespace Cpp
namespace SeqTailReplay2

/-!
# SeqTailReplay2: continuation package

A seq-tail continuation is the clean replacement target for old exact-tail
readiness transport.  It consists of post-state preservation plus tail statement
replay at the selected route.
-/

/--
A route-local package sufficient to start the seq tail in the selected
post-state.
-/
structure Package
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCI Γ σ s t σ1 P) : Type where
  postState : PostState route
  replay : StmtReplay route t

namespace Package

/-- The dynamic continuation boundary induced by post-state preservation and replay. -/
def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : Package route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  { state := h.postState.state
    safe := h.replay.ready }

/-- Compatibility view as the existing body dynamic boundary. -/
def toBodyDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCI Γ σ s t σ1 P}
    (h : Package route) :
    BodyDynamicBoundary route.Θ σ1 t :=
  h.toDynamicBoundary.toBodyDynamicBoundary

end Package

end SeqTailReplay2
end Cpp
