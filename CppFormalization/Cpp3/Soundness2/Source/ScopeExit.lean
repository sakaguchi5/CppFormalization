import CppFormalization.Cpp3.Soundness2.Source.LocalControl

/-!
# CppFormalization.Cpp3.Soundness2.Source.ScopeExit

Source theorem vocabulary for block scope exit.
-/

namespace Cpp3
namespace Soundness2
namespace Source

/-- Source for closing an opened block scope after the body has run. -/
structure BlockCloseSource
    (Γ Γopen Θ Δ : TypeEnv) (σbody σclosed : State) (body : StmtBlock) : Type where
  closeStability : Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body

namespace BlockCloseSource

/-- Project the close stability package. -/
def toCloseStability
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (h : BlockCloseSource Γ Γopen Θ Δ σbody σclosed body) :
    Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body :=
  h.closeStability

/-- Project the concrete runtime close step carried by stability. -/
def closeStep
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (h : BlockCloseSource Γ Γopen Θ Δ σbody σclosed body) :
    popScope? σbody = some σclosed :=
  h.closeStability.close.closeStep

end BlockCloseSource

/-- Source theorem for block-close stability. -/
structure BlockCloseSourceTheorem : Type where
  close :
    ∀ {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
      {r : CtrlResult} {σbody : State},
      Boundary.StmtBoundary Γ σ (.block body) →
      Boundary.BlockBoundary Γopen σopened body →
      Semantics.OpenedBlockRoute σ σopened body →
      Semantics.BigStepBlock σopened body r σbody →
        Σ Θ : TypeEnv,
          Σ Δ : TypeEnv,
            Σ σclosed : State,
              BlockCloseSource Γ Γopen Θ Δ σbody σclosed body

/-- Complete scope-exit source theorem bundle. -/
structure ScopeExitSourceTheorems : Type where
  blockClose : BlockCloseSourceTheorem

end Source
end Soundness2
end Cpp3
