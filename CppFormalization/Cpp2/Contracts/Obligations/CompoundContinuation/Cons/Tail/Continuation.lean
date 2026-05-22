import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Route

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail continuation

The continuation target of a cons-normal route is the block tail in the current
already-open block environment.
-/

structure PostState
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) : Prop where
  postState : PostStateAt Γ σ1

structure ReplayInvariant
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) : Prop where
  replay : BlockReplayAt Γ σ1 tail

structure ContinuationInput
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) : Prop where
  postState : PostState route
  replay : ReplayInvariant route

namespace ReplayInvariant

def ready
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (h : ReplayInvariant route) :
    BlockReadyConcrete Γ σ1 tail :=
  h.replay.ready

end ReplayInvariant

namespace ContinuationInput

def toDynamicBoundary
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    {route : HeadNormalRoute Γ σ σ1 head tail}
    (h : ContinuationInput route) :
    BlockContinuationDynamicBoundary Γ σ1 tail :=
  { state := h.postState.postState.state
    safe := h.replay.ready }

end ContinuationInput

end Tail
end Cons
end CompoundContinuation
end Cpp
