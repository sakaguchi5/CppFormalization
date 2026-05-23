import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.ReplayCore

namespace Cpp
namespace CompoundContinuation
namespace Cons

/-!
# Cons routes

A cons route is a selected operational route through an already-open/current
block tail `head :: tail`.

The mainline route is `HeadNormalRouteCore`: it records only the actual
head-normal execution.  The older `HeadNormalRoute` is kept as a legacy full
route because it also carries block-tail static/adequacy payload.  That payload
is not part of the operational route itself.
-/

structure TailStaticAdequacyPayload
    (Γ : TypeEnv) (σ1 : State) (ss : StmtBlock) : Type where
  static : BlockBodyStaticBoundaryCI Γ ss
  adequacy : BlockBodyAdequacyCI Γ σ1 ss static.profile

/--
Operational core of a selected cons head-normal route.

This is the C++/semantic route itself: the head statement executed normally and
reached the block-tail post-state.  It deliberately does not contain tail static
or adequacy payload.
-/
structure HeadNormalRouteCore
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hhead : BigStepStmt σ head .normal σ1

/--
Legacy full cons head-normal route.

This keeps the old payload-carrying shape for compatibility.  New continuation
and lifting APIs should use `HeadNormalRouteCore`; tail static/adequacy should be
projected separately when needed.
-/
structure HeadNormalRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hhead : BigStepStmt σ head .normal σ1
  tailPayload : TailStaticAdequacyPayload Γ σ1 tail

namespace HeadNormalRoute

/-- Forget the legacy tail payload and keep only the operational route core. -/
def toCore
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) :
    HeadNormalRouteCore Γ σ σ1 head tail :=
  { hhead := route.hhead }

end HeadNormalRoute

structure HeadBreakRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hhead : BigStepStmt σ head .breakResult σ1

structure HeadContinueRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hhead : BigStepStmt σ head .continueResult σ1

structure HeadReturnRoute
    (Γ : TypeEnv) (σ σ1 : State) (head : CppStmt) (tail : StmtBlock) (rv : Option Value) : Type where
  hhead : BigStepStmt σ head (.returnResult rv) σ1

structure HeadDivergesRoute
    (Γ : TypeEnv) (σ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  hheadDiv : BigStepStmtDiv σ head

end Cons
end CompoundContinuation
end Cpp
