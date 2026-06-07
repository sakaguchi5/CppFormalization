import CppFormalization.Cpp3.Boundary.Scope
import CppFormalization.Cpp3.Semantics.SelectedRoute.Basic

/-!
# CppFormalization.Cpp3.Boundary.Flow

Runtime boundaries at selected control-flow points.

This layer consumes `Semantics.SelectedRoute` and records the boundary that must
be present at the selected post-state.  It still does not prove that the boundary
is preserved; the proof-producing layer is `Stability`.
-/

namespace Cpp3
namespace Boundary

/-- Boundary for continuing from a normally completed sequence head to its tail. -/
structure SeqTailBoundary
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head tail : CppStmt) : Type where
  route : Semantics.SeqNormalRoute σ σ₁ head tail
  surface : Effects.SeqHeadEffectSurface Γ Θ head tail
  preserved : SafetyFragment.TailBoundaryFootprintPreserved Γ Θ head tail
  tail : StmtBoundary Θ σ₁ tail

/-- Boundary for continuing from a normally completed block head to its block tail. -/
structure BlockTailBoundary
    (Γ Θ : TypeEnv) (σ σ₁ : State) (head : CppStmt) (tail : StmtBlock) : Type where
  route : Semantics.BlockConsNormalRoute σ σ₁ head tail
  surface : Effects.BlockHeadEffectSurface Γ Θ head tail
  preserved : SafetyFragment.BlockTailBoundaryFootprintPreserved Γ Θ head tail
  tail : BlockBoundary Θ σ₁ tail

/-- Boundary for an if-statement selected branch. -/
inductive SelectedBranchBoundary
    (Γ Γc : TypeEnv) (σ σc : State) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Semantics.BranchSide → Type where
  | thenBoundary :
      Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch .thenBranch →
      CondBoundary Γ Γc σ cond →
      SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond thenBranch elseBranch →
      StmtBoundary Γc σc thenBranch →
      SelectedBranchBoundary Γ Γc σ σc cond thenBranch elseBranch .thenBranch

  | elseBoundary :
      Semantics.SelectedBranchRoute σ σc cond thenBranch elseBranch .elseBranch →
      CondBoundary Γ Γc σ cond →
      SafetyFragment.BranchBoundaryAfterConditionPreserved Γ Γc cond thenBranch elseBranch →
      StmtBoundary Γc σc elseBranch →
      SelectedBranchBoundary Γ Γc σ σc cond thenBranch elseBranch .elseBranch

/-- Boundary for a selected while boundary route.

For `exit` routes this records that condition evaluation itself was safe.  For
body/reentering routes the loop-safety package explains the intended safe C++
fragment, but the actual preservation proof is left to `Stability`. -/
structure WhileBoundary
    (Γ Γc : TypeEnv) (σ : State) (cond : CppCond) (body : CppStmt) : Type where
  route : Semantics.WhileBoundaryRoute σ cond body
  condition : CondBoundary Γ Γc σ cond
  surface : Effects.WhileEffectSurface Γ Γc cond body
  loopSafety : SafetyFragment.LoopSafetyFragment Γ Γc cond body
  backedgeBoundary : Prop
  backedgeEvidence : Contracts.Requires backedgeBoundary

/-- Boundary for the state reached after a while route. -/
def WhileBoundary.routePostState
    {Γ Γc : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (h : WhileBoundary Γ Γc σ cond body) : State :=
  Semantics.WhileBoundaryRoute.routePostState h.route

/-- Runtime route plus boundary for entering an opened block body. -/
structure RoutedOpenedBlockBoundary
    (Γ Γopen : TypeEnv) (σ σopened : State) (body : StmtBlock) : Type where
  route : Semantics.OpenedBlockRoute σ σopened body
  boundary : OpenedBlockBoundary Γ Γopen σ σopened body

end Boundary
end Cpp3
