import CppFormalization.Cpp2.Continuation.Compound.Seq.Tail.Components

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail continuation

A seq tail continuation is derived from post-state preservation plus route-local
runtime replay components at the selected core route's post-environment and
post-state.
-/

structure PostState
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  postState : PostStateAt route.Θ σ1

/--
Replay invariant for the selected seq tail route.

The invariant is now componentized: constructor replay, ordinary-read
non-clobbering, pointer/deref stability, and load-readability preservation are
recorded as route-local runtime replay components.  `StmtReplayAt` is then
materialized from those components.
-/
structure ReplayInvariant
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  components : RuntimeReplayComponentsAtRouteCI route

structure ContinuationInput
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  postState : PostState route
  replay : ReplayInvariant route

namespace ReplayInvariant

/-- Materialize the componentized route-local replay invariant. -/
def stmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : ReplayInvariant route) :
    StmtReplayAt route.Θ σ1 t :=
  h.components.toStmtReplay

def ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : ReplayInvariant route) :
    StmtReadyConcrete route.Θ σ1 t :=
  h.stmtReplay.ready

/--
Compatibility constructor from an already-materialized replay witness.

This keeps current callers small while making the future split explicit.  It
does not import or depend on the old `SeqTailReplay` obligation family.
-/
def ofStmtReplay
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : StmtReplayAt route.Θ σ1 t) :
    ReplayInvariant route :=
  { components := RuntimeReplayComponentsAtRouteCI.ofStmtReplay h }

end ReplayInvariant

namespace ContinuationInput

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : ContinuationInput route) :
    StmtContinuationDynamicBoundary route.Θ σ1 t :=
  { state := h.postState.postState.state
    safe := h.replay.ready }

def toBodyDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : ContinuationInput route) :
    BodyDynamicBoundary route.Θ σ1 t :=
  h.toDynamicBoundary.toBodyDynamicBoundary

end ContinuationInput

end Tail
end Seq
end CompoundContinuation
end Cpp
