import CppFormalization.Cpp3.Soundness.Instantiate.ScopeExit

/-!
# CppFormalization.Cpp3.Soundness.Derive.ScopeExit

Concrete construction layer for the scope-exit corridor theorem.

`Soundness.Instantiate.ScopeExit` introduced the C++-facing
`ScopeExitCorridorTheorem` consumed by the final soundness surface.  This file
moves one step lower: it describes how that corridor is obtained from the
already existing block-close stability package.

The intended separation is:

* `Instantiate.ScopeExit` says which scope-exit corridor the Soundness engine
  needs;
* this file says that the corridor is constructed from concrete
  `Stability.BlockCloseStability` facts, whose boundary already contains the
  `popScope?` close step and the lifetime-facing close safety surface.

No old provider-shaped field appears in the construction bundle below.
-/

namespace Cpp3
namespace Soundness
namespace Derive
namespace ScopeExit

/-- Lower-layer construction theorem for block-scope exit stability.

C++ reading: after executing an opened block body with any finite control result
(`normal`, `break`, `continue`, or `return`), the local scope can be closed in a
way justified by the block-close lifetime/effect boundary.  The returned
`Stability.BlockCloseStability` carries the concrete `Boundary.BlockCloseBoundary`,
including the `popScope?` step.
-/
structure BlockCloseStabilityConstructionTheorem : Type where
  closeStability :
    ∀ {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
      {r : CtrlResult} {σbody : State},
      Boundary.StmtBoundary Γ σ (.block body) →
      Boundary.BlockBoundary Γopen σopened body →
      Semantics.OpenedBlockRoute σ σopened body →
      Semantics.BigStepBlock σopened body r σbody →
        Σ Θ : TypeEnv,
          Σ Δ : TypeEnv,
            Σ σclosed : State,
              Stability.BlockCloseStability Γ Γopen Θ Δ σbody σclosed body

/-- Convert concrete block-close stability construction into a scope-exit corridor theorem. -/
def scopeExitCorridorTheorem_of_blockCloseStability
    (C : BlockCloseStabilityConstructionTheorem) :
    Instantiate.ScopeExit.ScopeExitCorridorTheorem where
  corridor := by
    intro Γ Γopen σ σopened body r σbody blockBoundary openedBody openedRoute bodyStep
    rcases C.closeStability blockBoundary openedBody openedRoute bodyStep with
      ⟨Θ, Δ, σclosed, closeStability⟩
    exact
      ⟨Θ, Δ, σclosed,
        {
          source := blockBoundary
          openedBody := openedBody
          openedRoute := openedRoute
          bodyStep := bodyStep
          closeStability := closeStability
        }⟩

/-- Concrete lower-layer theorem bundle for scope exit.

This is the second requested concretization target for the final soundness
surface: `scopeExit` is no longer supplied directly as the `Instantiate` corridor
interface; it is constructed from block-close stability facts.
-/
structure ScopeExitConstructionTheorems : Type where
  blockClose : BlockCloseStabilityConstructionTheorem

/-- Build the scope-exit corridor theorem from concrete lower-layer facts. -/
def scopeExitCorridorTheorem_of_construction
    (C : ScopeExitConstructionTheorems) :
    Instantiate.ScopeExit.ScopeExitCorridorTheorem :=
  scopeExitCorridorTheorem_of_blockCloseStability C.blockClose

end ScopeExit
end Derive
end Soundness
end Cpp3
