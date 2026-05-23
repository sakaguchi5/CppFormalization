import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Seq.Route

namespace Cpp
namespace CompoundContinuation
namespace Seq
namespace Tail

/-!
# Seq tail continuation

A seq tail continuation is derived from post-state preservation plus replay
at the selected core route's post-environment and post-state.
-/

structure PostState
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  postState : PostStateAt route.Θ σ1

structure ReplayInvariant
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  replay : StmtReplayAt route.Θ σ1 t

structure ContinuationInput
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    (route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P) : Prop where
  postState : PostState route
  replay : ReplayInvariant route

namespace ReplayInvariant

def ready
    {Γ : TypeEnv} {σ σ1 : State} {s t : CppStmt}
    {P : BodyControlProfile Γ s}
    {route : SeqHeadNormalRouteCoreCI Γ σ s t σ1 P}
    (h : ReplayInvariant route) :
    StmtReadyConcrete route.Θ σ1 t :=
  h.replay.ready

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
