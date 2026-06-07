import CppFormalization.Cpp3.Boundary.Stmt

/-!
# CppFormalization.Cpp3.Boundary.Scope

Runtime boundaries for block scope opening and closing.
-/

namespace Cpp3
namespace Boundary

/-- Boundary for entering an opened block body. -/
structure OpenedBlockBoundary
    (Γ Γopen : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type where
  static : Static.StaticOpenedBlockBoundaryInfo Γ Γopen body
  effect : Effects.OpenedBlockEffectSurface Γ Γopen body
  route : Semantics.OpenedBlockRoute σ σopened body
  bodyBoundary : BlockBoundary Γopen σopened body

/-- Boundary for a block scope effect. -/
structure BlockScopeBoundary
    (Γ Γopen Θ Δ : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type where
  effect : Effects.BlockScopeEffect Γ Γopen Θ Δ body
  opened : OpenedBlockBoundary Γ Γopen σ σopened body
  closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body

/-- Boundary for closing a block scope after the opened body has produced a state. -/
structure BlockCloseBoundary
    (Γ Γopen Θ Δ : TypeEnv) (σbody σclosed : State) (body : StmtBlock) : Type where
  closeEffect : Effects.BlockCloseLifetimeEffect Γ Γopen Θ Δ body
  closeSafe : SafetyFragment.BlockCloseLifetimeSafety Γ Γopen Θ Δ body
  closeStep : popScope? σbody = some σclosed

end Boundary
end Cpp3
