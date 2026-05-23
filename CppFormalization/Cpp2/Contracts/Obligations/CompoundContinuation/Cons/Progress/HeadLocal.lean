import CppFormalization.Cpp2.Contracts.Obligations.CompoundContinuation.Cons.Route

namespace Cpp
namespace CompoundContinuation
namespace Cons

/-!
# Cons head-local progress demand

This is proof architecture, not a C++ replay contract.  The head of
`head :: tail` must be classified as one of the local outcomes understood by
block semantics.

The normal outcome uses `HeadNormalRouteCore`; tail static/adequacy is not part
of head-local progress.
-/

inductive HeadLocalOutcome
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock} : Type where
  | normal (σ1 : State) :
      HeadNormalRouteCore Γ σ σ1 head tail →
      HeadLocalOutcome
  | broke (σ1 : State) :
      HeadBreakRoute Γ σ σ1 head tail →
      HeadLocalOutcome
  | continued (σ1 : State) :
      HeadContinueRoute Γ σ σ1 head tail →
      HeadLocalOutcome
  | returned (rv : Option Value) (σ1 : State) :
      HeadReturnRoute Γ σ σ1 head tail rv →
      HeadLocalOutcome
  | diverged :
      HeadDivergesRoute Γ σ head tail →
      HeadLocalOutcome

namespace HeadLocalOutcome

/-- Compatibility helper for callers that still hold the legacy full route. -/
def normalOfLegacy
    {Γ : TypeEnv} {σ σ1 : State} {head : CppStmt} {tail : StmtBlock}
    (route : HeadNormalRoute Γ σ σ1 head tail) :
    HeadLocalOutcome (Γ := Γ) (σ := σ) (head := head) (tail := tail) :=
  HeadLocalOutcome.normal σ1 route.toCore

end HeadLocalOutcome

structure HeadLocalProgress
    (Γ : TypeEnv) (σ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  outcome : HeadLocalOutcome (Γ := Γ) (σ := σ) (head := head) (tail := tail)

end Cons
end CompoundContinuation
end Cpp
