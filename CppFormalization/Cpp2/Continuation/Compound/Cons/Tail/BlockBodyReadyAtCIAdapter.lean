import CppFormalization.Cpp2.Entry.Body.BlockBodyReadyAtCI
import CppFormalization.Cpp2.Continuation.Compound.Cons.Tail.Continuation

namespace Cpp
namespace CompoundContinuation
namespace Cons
namespace Tail

/-!
# Cons tail adapter for CI-native block-body readiness

This file connects the route-local compound continuation package to the new
current-env block-body closure surface.

The key point is that the block-body closure consumes only a dynamic tail
boundary.  The reason why that boundary exists belongs here, in the
CompoundContinuation route-local layer.
-/

/--
Provider of route-local continuation input for cons-normal block tails.

The route is indexed by the residual/tail environment `Θ`, not the pre-head
environment `Γ`.
-/
abbrev ContinuationInputProviderForBlockBodyReadyAtCI : Prop :=
  ∀ {Γ Θ : TypeEnv} {σ σ' : State} {head : CppStmt} {tail : StmtBlock},
    BlockBodyReadyAtCI Γ σ (.cons head tail) →
    HasTypeStmtCI .normalK Γ head Θ →
    (route : HeadNormalRouteCore Θ σ σ' head tail) →
    ContinuationInput route

/--
Turn route-local compound continuation input into the dynamic tail provider
consumed by CI-native opened block-body closure.
-/
def tailDynamicProvider_of_continuationInputProvider
    (mkInput : ContinuationInputProviderForBlockBodyReadyAtCI) :
    BlockBodyReadyAtCITailDynamicProvider := by
  intro Γ Θ σ σ' head tail hready hhead hstep
  let route : HeadNormalRouteCore Θ σ σ' head tail :=
    { hhead := hstep }
  exact (mkInput hready hhead route).toDynamicBoundary

end Tail
end Cons
end CompoundContinuation
end Cpp
