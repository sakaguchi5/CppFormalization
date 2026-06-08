import CppFormalization.Cpp3.Static.Entry
import CppFormalization.Cpp3.Static.FunctionBodyControl

/-!
# CppFormalization.Cpp3.Static.BoundaryInfo

Static boundary information, not runtime readiness.

This file should not be confused with the later `Boundary` layer.  The later
runtime Boundary layer will mention concrete states and explain when expressions,
conditions, statements, and blocks can actually be entered.  This file only
packages the static, state-free information visible before runtime execution.
-/

namespace Cpp3
namespace Static

/-- Static expression boundary information. -/
structure StaticValBoundaryInfo (Γ : TypeEnv) (e : ValExpr) : Type where
  formed : StaticValFormed e

/-- Static place boundary information. -/
structure StaticPlaceBoundaryInfo (Γ : TypeEnv) (p : PlaceExpr) : Type where
  formed : StaticPlaceFormed p

/-- Static condition boundary information. -/
structure StaticCondBoundaryInfo (Γ Γc : TypeEnv) (cond : CppCond) : Type where
  formed : StaticCondFormed cond

/-- Static statement boundary information. -/
structure StaticStmtBoundaryInfo (Γ : TypeEnv) (st : CppStmt) : Type where
  entry : StmtEntryWitness Γ st

/-- Static block-body boundary information. -/
structure StaticBlockBoundaryInfo (Γ : TypeEnv) (ss : StmtBlock) : Type where
  entry : BlockEntryWitness Γ ss

/-- Static function-body boundary information.

A function body may finish normally or return; uncaught break/continue are not
function-body successes.  The `control` field makes that exclusion part of the
static boundary, rather than a later ad-hoc runtime provider. -/
structure StaticFunctionBodyBoundaryInfo (Γ : TypeEnv) (body : CppStmt) : Type where
  entry : StmtEntryWitness Γ body
  control : FunctionBodyControlSurface body
  normalSurface : entry.profile.canControl .normalK → StaticStmtControl body .normalK :=
    entry.profile.sound
  returnSurface : entry.profile.canControl .returnK → StaticStmtControl body .returnK :=
    entry.profile.sound

/-- Static boundary information for a sequence tail. -/
structure StaticSeqTailBoundaryInfo
    (Γ Θ : TypeEnv) (head tail : CppStmt) : Type where
  tailEntry : SeqTailEntry Γ Θ head tail

/-- Static boundary information for a block tail. -/
structure StaticBlockTailBoundaryInfo
    (Γ Θ : TypeEnv) (head : CppStmt) (tail : StmtBlock) : Type where
  tailEntry : BlockTailEntry Γ Θ head tail

/-- Static boundary information for a selected branch. -/
structure StaticSelectedBranchBoundaryInfo
    (Γ Γc : TypeEnv) (cond : CppCond)
    (thenBranch elseBranch : CppStmt) : Type where
  choice : StaticBranchChoice
  branchEntry : SelectedBranchEntry Γ Γc cond thenBranch elseBranch choice

/-- Static boundary information for a while backedge. -/
structure StaticWhileBackedgeBoundaryInfo
    (Γ Γc : TypeEnv) (cond : CppCond) (body : CppStmt) : Type where
  entry : WhileEntry Γ Γc cond body

/-- Static boundary information for an opened block body. -/
structure StaticOpenedBlockBoundaryInfo
    (Γ Γopen : TypeEnv) (body : StmtBlock) : Type where
  entry : OpenedBlockEntry Γ Γopen body

end Static
end Cpp3
