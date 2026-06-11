import CppFormalization.Cpp3.Soundness2.Realize.Stability
import CppFormalization.Cpp3.Soundness2.Source.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ScopeExit

Realized scope-exit theorem bundle for the closed-internal Soundness2 route.

This layer restores the lower bridge from block-close stability to the
scope-exit theorem surface.  C++ block execution has a real close step after the
opened block body, so this is deliberately separate from local control.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Realize a scope-exit block-close source from block-close stability. -/
def blockCloseSource_of_stability
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (closeStability : Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body) :
    Source.BlockCloseSource Γ Γopen Θ Δ σbody σclosed body where
  closeStability := closeStability

/-- Build the scope-exit source theorem from a lower block-close-stability theorem. -/
def blockCloseSourceTheorem_of_stabilityTheorem
    (close :
      ∀ {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
        {r : CtrlResult} {σbody : State},
        Boundary.StmtBoundary Γ σ (.block body) →
        Boundary.BlockBoundary Γopen σopened body →
        Semantics.OpenedBlockRoute σ σopened body →
        Semantics.BigStepBlock σopened body r σbody →
          Σ Θ : TypeEnv,
            Σ Δ : TypeEnv,
              Σ σclosed : State,
                Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body) :
    Source.BlockCloseSourceTheorem where
  close := by
    intro Γ Γopen σ σopened body r σbody blockBoundary openedBody openedRoute bodyStep
    rcases close blockBoundary openedBody openedRoute bodyStep with
      ⟨Θ, Δ, σclosed, closeStability⟩
    exact ⟨Θ, Δ, σclosed, blockCloseSource_of_stability closeStability⟩

/-- Realizer bundle for scope-exit source theorems. -/
structure ScopeExitRealizationTheorems : Type where
  blockClose : Source.BlockCloseSourceTheorem

namespace ScopeExitRealizationTheorems

/-- Convert realized scope-exit theorem pieces into the source bundle. -/
def toSourceTheorems
    (R : ScopeExitRealizationTheorems) :
    Source.ScopeExitSourceTheorems where
  blockClose := R.blockClose

end ScopeExitRealizationTheorems

end Realize
end Soundness2
end Cpp3
