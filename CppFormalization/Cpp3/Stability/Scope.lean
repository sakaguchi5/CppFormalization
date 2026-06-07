import CppFormalization.Cpp3.Stability.Flow
import CppFormalization.Cpp3.Boundary.Scope

/-!
# CppFormalization.Cpp3.Stability.Scope

Stability packages for block scope opening and closing.

Scope stability is where lifetime-facing safety fragments meet concrete runtime
scope transitions.  The actual no-dangling theorem can be added later by
constructing these packages from lower invariants.
-/

namespace Cpp3
namespace Stability

/-- Stability of the opened block body boundary. -/
structure BlockScopeOpenStability
    (Γ Γopen Θ Δ : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type 1 where
  boundary : Boundary.BlockScopeBoundary Γ Γopen Θ Δ σ σopened body
  openedStable : OpenedBlockStability Γ Γopen σ σopened body
  certificate : StabilityCertificate .stabilityDerived

/-- Stability of closing a block scope after the opened body has run. -/
structure BlockCloseStability
    (Γ Γopen Θ Δ : TypeEnv) (σbody σclosed : State) (body : StmtBlock) : Type where
  close : Boundary.BlockCloseBoundary Γ Γopen Θ Δ σbody σclosed body
  certificate : StabilityCertificate .stabilityDerived

/-- A complete scope-transition stability package for a block statement. -/
structure BlockScopeStability
    (Γ Γopen Θ Δ : TypeEnv)
    (σ σopened σbody σclosed : State) (body : StmtBlock) : Type 1 where
  opened : BlockScopeOpenStability Γ Γopen Θ Δ σ σopened body
  bodyResult : BlockResultStability Γopen σopened σbody body .normal
  closed : BlockCloseStability Γ Γopen Θ Δ σbody σclosed body
  certificate : StabilityCertificate .stabilityDerived

end Stability
end Cpp3
