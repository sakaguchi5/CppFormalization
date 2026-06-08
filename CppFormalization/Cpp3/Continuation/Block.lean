import CppFormalization.Cpp3.Continuation.Seq
import CppFormalization.Cpp3.Stability.Scope

/-!
# CppFormalization.Cpp3.Continuation.Block

Continuation surfaces for block bodies and block scopes.
-/

namespace Cpp3
namespace Continuation

/-- Continuation from a normally completed block head to its block tail. -/
structure BlockTailContinuation
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  stability : Stability.BlockTailStability Γ Θ σ σ₁ head tail

namespace BlockTailContinuation

/-- The source boundary for the whole block cons. -/
def source
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailContinuation Γ Θ σ σ₁ head tail) :
    Boundary.BlockBoundary Γ σ (.cons head tail) :=
  h.stability.source

/-- The selected normal route through the block head. -/
def route
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailContinuation Γ Θ σ σ₁ head tail) :
    Semantics.BlockConsNormalRoute σ σ₁ head tail :=
  h.stability.target.route

/-- The complete target boundary package for the block tail. -/
def target
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailContinuation Γ Θ σ σ₁ head tail) :
    Boundary.BlockTailBoundary Γ Θ σ σ₁ head tail :=
  h.stability.target

/-- The block boundary consumed by the next execution step. -/
def tailBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailContinuation Γ Θ σ σ₁ head tail) :
    Boundary.BlockBoundary Θ σ₁ tail :=
  h.stability.target.tail

end BlockTailContinuation

/-- Continuation from a block statement into its opened block body. -/
structure OpenedBlockContinuation
    (Γ Γopen : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type where
  stability : Stability.OpenedBlockStability Γ Γopen σ σopened body

namespace OpenedBlockContinuation

/-- The source boundary for the block statement. -/
def source
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : OpenedBlockContinuation Γ Γopen σ σopened body) :
    Boundary.StmtBoundary Γ σ (.block body) :=
  h.stability.source

/-- The routed opened-block boundary. -/
def target
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : OpenedBlockContinuation Γ Γopen σ σopened body) :
    Boundary.RoutedOpenedBlockBoundary Γ Γopen σ σopened body :=
  h.stability.target

/-- The opened body boundary consumed by block-body execution. -/
def openedBodyBoundary
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : OpenedBlockContinuation Γ Γopen σ σopened body) :
    Boundary.BlockBoundary Γopen σopened body :=
  h.stability.target.boundary.bodyBoundary

end OpenedBlockContinuation

/-- Continuation package for the whole block scope open/body/close corridor. -/
structure BlockScopeContinuation
    (Γ Γopen Θ Δ : TypeEnv)
    (σ σopened σbody σclosed : State) (body : StmtBlock) : Type where
  stability : Stability.BlockScopeStability Γ Γopen Θ Δ σ σopened σbody σclosed body

namespace BlockScopeContinuation

/-- Boundary for the opened block body. -/
def openedBodyBoundary
    {Γ Γopen Θ Δ : TypeEnv}
    {σ σopened σbody σclosed : State} {body : StmtBlock}
    (h : BlockScopeContinuation Γ Γopen Θ Δ σ σopened σbody σclosed body) :
    Boundary.BlockBoundary Γopen σopened body :=
  h.stability.opened.openedStable.target.boundary.bodyBoundary

/-- Boundary for closing the block scope after the body. -/
def closeBoundary
    {Γ Γopen Θ Δ : TypeEnv}
    {σ σopened σbody σclosed : State} {body : StmtBlock}
    (h : BlockScopeContinuation Γ Γopen Θ Δ σ σopened σbody σclosed body) :
    Boundary.BlockCloseBoundary Γ Γopen Θ Δ σbody σclosed body :=
  h.stability.closed.close

end BlockScopeContinuation

end Continuation
end Cpp3
