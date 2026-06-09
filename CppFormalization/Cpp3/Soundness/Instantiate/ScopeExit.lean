import CppFormalization.Cpp3.Soundness.Instantiate.Providers
import CppFormalization.Cpp3.Stability.Scope

/-!
# CppFormalization.Cpp3.Soundness.Instantiate.ScopeExit

Scope-exit corridor instantiation for `BlockCloseProvider`.

The remaining block-close provider is not local control-flow glue.  It is the
C++ scope/lifetime handoff that happens after an opened block body has produced a
finite control result.  This file names that handoff as a `ScopeExitCorridor` and
turns it into the old provider shape by projecting the concrete `popScope?`
close step already carried by `Boundary.BlockCloseBoundary`.

This file does not prove that all safe block bodies can be closed.  It only
separates the C++-facing scope/lifetime corridor from the Soundness provider
interface, so later lower-layer files can construct the corridor from concrete
scope/lifetime preservation facts.
-/

namespace Cpp3
namespace Soundness
namespace Instantiate
namespace ScopeExit

/-- C++ corridor for closing a block scope after the opened body has run.

C++ reading: after executing the opened block body with any finite control result
(`normal`, `break`, `continue`, or `return`), the local block scope can be closed
without leaving the outer runtime state ill-formed.  The actual runtime close step
is stored inside `closeStability.close.closeStep`.
-/
structure ScopeExitCorridor
    (Γ Γopen Θ Δ : TypeEnv)
    (σ σopened σbody σclosed : State)
    (body : StmtBlock) (r : CtrlResult) : Type where
  source : Boundary.StmtBoundary Γ σ (.block body)
  openedBody : Boundary.BlockBoundary Γopen σopened body
  openedRoute : Semantics.OpenedBlockRoute σ σopened body
  bodyStep : Semantics.BigStepBlock σopened body r σbody
  closeStability : Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body

namespace ScopeExitCorridor

/-- Project the concrete runtime scope-close step carried by the corridor. -/
def closeStep
    {Γ Γopen Θ Δ : TypeEnv}
    {σ σopened σbody σclosed : State}
    {body : StmtBlock} {r : CtrlResult}
    (h : ScopeExitCorridor Γ Γopen Θ Δ σ σopened σbody σclosed body r) :
    popScope? σbody = some σclosed :=
  h.closeStability.close.closeStep

/-- Project the block-close boundary behind the stability package. -/
def closeBoundary
    {Γ Γopen Θ Δ : TypeEnv}
    {σ σopened σbody σclosed : State}
    {body : StmtBlock} {r : CtrlResult}
    (h : ScopeExitCorridor Γ Γopen Θ Δ σ σopened σbody σclosed body r) :
    Boundary.BlockCloseBoundary Γ Γopen Θ Δ σbody σclosed body :=
  h.closeStability.close

end ScopeExitCorridor

/-- Lower-layer theorem surface for constructing scope-exit corridors.

The existential `Θ` and `Δ` keep the Soundness-facing provider independent of the
particular static environments used by the scope/lifetime layer. -/
structure ScopeExitCorridorTheorem : Type where
  corridor :
    ∀ {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
      {r : CtrlResult} {σbody : State},
      Boundary.StmtBoundary Γ σ (.block body) →
      Boundary.BlockBoundary Γopen σopened body →
      Semantics.OpenedBlockRoute σ σopened body →
      Semantics.BigStepBlock σopened body r σbody →
        Σ Θ : TypeEnv,
          Σ Δ : TypeEnv,
            Σ σclosed : State,
              ScopeExitCorridor Γ Γopen Θ Δ σ σopened σbody σclosed body r

/-- `BlockCloseProvider` is just the projection of a `ScopeExitCorridor`.

This is the promised `ScopeExitCorridor → BlockCloseProvider` bridge.  It does
not hide the scope/lifetime obligation; it moves that obligation to the corridor
construction theorem and leaves Soundness with only the old provider interface. -/
def blockCloseProvider_of_scopeExit
    (C : ScopeExitCorridorTheorem) :
    BlockCloseProvider where
  close := by
    intro Γ Γopen σ σopened body r σbody blockBoundary openedBody openedRoute bodyStep
    rcases C.corridor blockBoundary openedBody openedRoute bodyStep with
      ⟨_Θ, _Δ, σclosed, corridor⟩
    exact ⟨σclosed, corridor.closeStep⟩

end ScopeExit
end Instantiate
end Soundness
end Cpp3
