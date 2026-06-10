import CppFormalization.Cpp3.Soundness.Derive.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness.Derive.ScopeExit.Constructors

Bottom-up constructors for scope-exit construction facts.

`Derive.ScopeExit` already names the construction theorem surface that turns
block-close stability into the scope-exit corridor consumed by final soundness.
This file fixes the construction direction for that surface: the smallest
scope-exit evidence is the concrete `Stability.BlockCloseStability` fact, and the
existing theorem bundle is built from sources that supply that fact.

C++ reading: after an opened block body finishes with a finite control result, the
block-local scope can be closed without leaking invalid lifetime assumptions to
the outer state.  The source below carries exactly that close stability evidence.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace ScopeExit

/-- Bottom-up source for closing an opened block scope after the body has run. -/
structure BlockCloseSource
    (Γ Γopen Θ Δ : TypeEnv) (σbody σclosed : State) (body : StmtBlock) : Type where
  closeStability : Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body

namespace BlockCloseSource

/-- Project the concrete block-close stability fact. -/
def toCloseStability
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (h : BlockCloseSource Γ Γopen Θ Δ σbody σclosed body) :
    Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body :=
  h.closeStability

/-- Project the concrete runtime `popScope?` close step carried by stability. -/
def closeStep
    {Γ Γopen Θ Δ : TypeEnv} {σbody σclosed : State} {body : StmtBlock}
    (h : BlockCloseSource Γ Γopen Θ Δ σbody σclosed body) :
    popScope? σbody = some σclosed :=
  h.closeStability.close.closeStep

end BlockCloseSource

/-- Bottom-up theorem surface for producing block-close sources. -/
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

/-- Convert bottom-up block-close sources to the existing construction theorem. -/
def blockCloseStabilityConstructionTheorem_of_source
    (C : BlockCloseSourceTheorem) :
    BlockCloseStabilityConstructionTheorem where
  closeStability := by
    intro Γ Γopen σ σopened body r σbody blockBoundary openedBody openedRoute bodyStep
    rcases C.close blockBoundary openedBody openedRoute bodyStep with
      ⟨Θ, Δ, σclosed, source⟩
    exact ⟨Θ, Δ, σclosed, source.toCloseStability⟩

/-- Bottom-up source bundle for scope-exit construction facts. -/
structure ScopeExitSourceTheorems : Type where
  blockClose : BlockCloseSourceTheorem

/-- Build the existing scope-exit construction bundle from bottom-up sources. -/
def scopeExitConstructionTheorems_of_sources
    (C : ScopeExitSourceTheorems) :
    ScopeExitConstructionTheorems where
  blockClose := blockCloseStabilityConstructionTheorem_of_source C.blockClose

/-- Compose bottom-up scope-exit sources directly to the scope-exit corridor theorem. -/
def scopeExitCorridorTheorem_of_sources
    (C : ScopeExitSourceTheorems) :
    Instantiate.ScopeExit.ScopeExitCorridorTheorem :=
  scopeExitCorridorTheorem_of_construction
    (scopeExitConstructionTheorems_of_sources C)

end ScopeExit
end Derive
end Soundness
end Cpp3
