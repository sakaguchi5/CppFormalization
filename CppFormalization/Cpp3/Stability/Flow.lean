import CppFormalization.Cpp3.Stability.Stmt
import CppFormalization.Cpp3.Boundary.Flow

/-!
# CppFormalization.Cpp3.Stability.Flow

Stability packages for selected control-flow boundaries.

This is the heart of the layer: selected semantic routes are paired directly
with the post-state boundary that later `Continuation` should consume.  The
certificate proposition is visible rather than hidden behind a generic opaque
boundary wrapper.
-/

namespace Cpp3
namespace Stability

/-- Stability of the sequence tail boundary after a normally completed head. -/
structure SeqTailStability
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  source : Boundary.StmtBoundary Γ σ (.seq head tail)
  target : Boundary.SeqTailBoundary Γ Θ σ σ₁ head tail
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

namespace SeqTailStability

/-- Project the concrete tail boundary. -/
def tailBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt}
    (h : SeqTailStability Γ Θ σ σ₁ head tail) :
    Boundary.SeqTailBoundary Γ Θ σ σ₁ head tail :=
  h.target

end SeqTailStability

/-- Stability of the block tail boundary after a normally completed block head. -/
structure BlockTailStability
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  source : Boundary.BlockBoundary Γ σ (.cons head tail)
  target : Boundary.BlockTailBoundary Γ Θ σ σ₁ head tail
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

namespace BlockTailStability

/-- Project the concrete block-tail boundary. -/
def tailBoundary
    {Γ Θ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock}
    (h : BlockTailStability Γ Θ σ σ₁ head tail) :
    Boundary.BlockTailBoundary Γ Θ σ σ₁ head tail :=
  h.target

end BlockTailStability

/-- Stability of the branch boundary selected by an `if` condition. -/
structure SelectedBranchStability
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) (side : Semantics.BranchSide) : Type where
  source : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch)
  target : Boundary.SelectedBranchBoundary Γ Γc σ σc cond thenBranch elseBranch side
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

namespace SelectedBranchStability

/-- Project the selected branch boundary. -/
def branchBoundary
    {Γ Γc : TypeEnv} {σ σc : State} {cond : CppCond}
    {thenBranch elseBranch : CppStmt} {side : Semantics.BranchSide}
    (h : SelectedBranchStability Γ Γc σ σc cond thenBranch elseBranch side) :
    Boundary.SelectedBranchBoundary Γ Γc σ σc cond thenBranch elseBranch side :=
  h.target

end SelectedBranchStability

/-- Stability of a selected while boundary route. -/
structure WhileBoundaryStability
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  source : Boundary.StmtBoundary Γ σ (.whileStmt cond body)
  target : Boundary.WhileBoundary Γ Γc σ cond body
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

namespace WhileBoundaryStability

/-- Project the while boundary. -/
def whileBoundary
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundaryStability Γ Γc σ cond body) :
    Boundary.WhileBoundary Γ Γc σ cond body :=
  h.target

/-- The post-state reached by the selected while route. -/
def routePostState
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundaryStability Γ Γc σ cond body) : State :=
  h.whileBoundary.routePostState

end WhileBoundaryStability

/-- Stability of opening a block and entering its opened body. -/
structure OpenedBlockStability
    (Γ Γopen : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type where
  source : Boundary.StmtBoundary Γ σ (.block body)
  target : Boundary.RoutedOpenedBlockBoundary Γ Γopen σ σopened body
  stable : Prop
  certificate : StabilityCertificate .stabilityDerived stable

namespace OpenedBlockStability

/-- Project the opened-block boundary. -/
def openedBoundary
    {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
    (h : OpenedBlockStability Γ Γopen σ σopened body) :
    Boundary.RoutedOpenedBlockBoundary Γ Γopen σ σopened body :=
  h.target

end OpenedBlockStability

end Stability
end Cpp3
