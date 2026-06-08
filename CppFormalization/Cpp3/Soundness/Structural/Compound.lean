import CppFormalization.Cpp3.Soundness.Structural.Primitive

/-!
# CppFormalization.Cpp3.Soundness.Structural.Compound

Constructor-local soundness clauses for compound statements, block bodies, and
function bodies in the closed internal C++ fragment.

The key design point is that compound clauses do not hide continuation demands:
seq/block tails, selected branches, while reentry, and opened block bodies are
exposed as callbacks over the existing `Continuation` surfaces.
-/

namespace Cpp3
namespace Soundness
namespace Structural

/-- Structural soundness clause for statement sequencing.

C++ reading: if the head is classified, and every normal-head continuation into
the tail can classify the tail, then the whole `head; tail` sequence is
classified.  Abrupt and diverging head paths are handled by the constructor-local
proof that will later instantiate this clause. -/
structure SeqStructuralSoundnessClause : Type where
  sound :
    ∀ {Γ : TypeEnv} {σ : State} {head tail : CppStmt},
      Boundary.StmtBoundary Γ σ (.seq head tail) →
      ClosedStmtSoundness σ head →
      (∀ {Θ : TypeEnv} {σ₁ : State},
        Continuation.SeqTailContinuation Γ Θ σ σ₁ head tail →
          ClosedStmtSoundness σ₁ tail) →
      ClosedStmtSoundness σ (.seq head tail)

/-- Structural soundness clause for selected if-branches. -/
structure BranchStructuralSoundnessClause : Type where
  sound :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
      (∀ {Γc : TypeEnv} {σc : State},
        Continuation.ThenBranchContinuation Γ Γc σ σc cond thenBranch elseBranch →
          ClosedStmtSoundness σc thenBranch) →
      (∀ {Γc : TypeEnv} {σc : State},
        Continuation.ElseBranchContinuation Γ Γc σ σc cond thenBranch elseBranch →
          ClosedStmtSoundness σc elseBranch) →
      ClosedStmtSoundness σ (.ite cond thenBranch elseBranch)

/-- Structural soundness clause for while-statements.

The clause intentionally separates ordinary body soundness from loop reentry
soundness.  This mirrors C++ execution: a body-normal/body-continue path must
return to the guard, while exit/break/return paths classify the loop without a
termination assumption. -/
structure WhileStructuralSoundnessClause : Type where
  sound :
    ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
      Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      (∀ {Γbody : TypeEnv} {σbody : State},
        Boundary.StmtBoundary Γbody σbody body →
          ClosedStmtSoundness σbody body) →
      (∀ {Γc : TypeEnv} {σreentry : State} {Reentry : Prop},
        Continuation.WhileReentryContinuation Γ Γc σ σreentry cond body Reentry →
          ClosedStmtSoundness σreentry (.whileStmt cond body)) →
      ClosedStmtSoundness σ (.whileStmt cond body)

/-- Structural soundness clause for block statements.

A block statement opens a scope, runs the opened body, and closes the scope.  The
opened-body classification is deliberately a callback over the block boundary so
later proof files can connect it to `OpenedBlockContinuation`/scope stability. -/
structure BlockStmtStructuralSoundnessClause : Type where
  sound :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Boundary.StmtBoundary Γ σ (.block body) →
      (∀ {Γopen : TypeEnv} {σopened : State},
        Boundary.BlockBoundary Γopen σopened body →
          ClosedBlockSoundness σopened body) →
      ClosedStmtSoundness σ (.block body)

/-- Structural soundness clause for an empty block body. -/
structure BlockNilStructuralSoundnessClause : Type where
  sound :
    ∀ {Γ : TypeEnv} {σ : State},
      Boundary.BlockBoundary Γ σ .nil →
      ClosedBlockSoundness σ .nil

/-- Structural soundness clause for block-body cons.

C++ reading: classify the head, and for every normal-head route that exposes the
block tail, classify that tail at the route post-state. -/
structure BlockConsStructuralSoundnessClause : Type where
  sound :
    ∀ {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock},
      Boundary.BlockBoundary Γ σ (.cons head tail) →
      ClosedStmtSoundness σ head →
      (∀ {Θ : TypeEnv} {σ₁ : State},
        Continuation.BlockTailContinuation Γ Θ σ σ₁ head tail →
          ClosedBlockSoundness σ₁ tail) →
      ClosedBlockSoundness σ (.cons head tail)

/-- Structural soundness clause for function bodies.

This is separate from statement soundness because function-body finite success
excludes uncaught top-level `break` and `continue`. -/
structure FunctionBodyStructuralSoundnessClause : Type where
  sound :
    ∀ {Γ : TypeEnv} {σ : State} {body : CppStmt},
      Boundary.FunctionBodyBoundary Γ σ body →
      (Boundary.StmtBoundary Γ σ body → ClosedStmtSoundness σ body) →
      ClosedFunctionBodySoundness σ body

namespace SeqStructuralSoundnessClause

/-- Apply the sequencing structural soundness clause. -/
theorem closed
    (C : SeqStructuralSoundnessClause)
    {Γ : TypeEnv} {σ : State} {head tail : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.seq head tail))
    (headSound : ClosedStmtSoundness σ head)
    (tailSound :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        Continuation.SeqTailContinuation Γ Θ σ σ₁ head tail →
          ClosedStmtSoundness σ₁ tail) :
    ClosedStmtSoundness σ (.seq head tail) :=
  C.sound boundary headSound tailSound

end SeqStructuralSoundnessClause

namespace BranchStructuralSoundnessClause

/-- Apply the selected-branch structural soundness clause. -/
theorem closed
    (C : BranchStructuralSoundnessClause)
    {Γ : TypeEnv} {σ : State}
    {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch))
    (thenSound :
      ∀ {Γc : TypeEnv} {σc : State},
        Continuation.ThenBranchContinuation Γ Γc σ σc cond thenBranch elseBranch →
          ClosedStmtSoundness σc thenBranch)
    (elseSound :
      ∀ {Γc : TypeEnv} {σc : State},
        Continuation.ElseBranchContinuation Γ Γc σ σc cond thenBranch elseBranch →
          ClosedStmtSoundness σc elseBranch) :
    ClosedStmtSoundness σ (.ite cond thenBranch elseBranch) :=
  C.sound boundary thenSound elseSound

end BranchStructuralSoundnessClause

namespace WhileStructuralSoundnessClause

/-- Apply the while structural soundness clause. -/
theorem closed
    (C : WhileStructuralSoundnessClause)
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.whileStmt cond body))
    (bodySound :
      ∀ {Γbody : TypeEnv} {σbody : State},
        Boundary.StmtBoundary Γbody σbody body →
          ClosedStmtSoundness σbody body)
    (reentrySound :
      ∀ {Γc : TypeEnv} {σreentry : State} {Reentry : Prop},
        Continuation.WhileReentryContinuation Γ Γc σ σreentry cond body Reentry →
          ClosedStmtSoundness σreentry (.whileStmt cond body)) :
    ClosedStmtSoundness σ (.whileStmt cond body) :=
  C.sound boundary bodySound reentrySound

end WhileStructuralSoundnessClause

namespace BlockStmtStructuralSoundnessClause

/-- Apply the block-statement structural soundness clause. -/
theorem closed
    (C : BlockStmtStructuralSoundnessClause)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.StmtBoundary Γ σ (.block body))
    (bodySound :
      ∀ {Γopen : TypeEnv} {σopened : State},
        Boundary.BlockBoundary Γopen σopened body →
          ClosedBlockSoundness σopened body) :
    ClosedStmtSoundness σ (.block body) :=
  C.sound boundary bodySound

end BlockStmtStructuralSoundnessClause

namespace BlockNilStructuralSoundnessClause

/-- Apply the nil-block structural soundness clause. -/
theorem closed
    (C : BlockNilStructuralSoundnessClause)
    {Γ : TypeEnv} {σ : State}
    (boundary : Boundary.BlockBoundary Γ σ .nil) :
    ClosedBlockSoundness σ .nil :=
  C.sound boundary

end BlockNilStructuralSoundnessClause

namespace BlockConsStructuralSoundnessClause

/-- Apply the block-cons structural soundness clause. -/
theorem closed
    (C : BlockConsStructuralSoundnessClause)
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ (.cons head tail))
    (headSound : ClosedStmtSoundness σ head)
    (tailSound :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        Continuation.BlockTailContinuation Γ Θ σ σ₁ head tail →
          ClosedBlockSoundness σ₁ tail) :
    ClosedBlockSoundness σ (.cons head tail) :=
  C.sound boundary headSound tailSound

end BlockConsStructuralSoundnessClause

namespace FunctionBodyStructuralSoundnessClause

/-- Apply the function-body structural soundness clause. -/
theorem closed
    (C : FunctionBodyStructuralSoundnessClause)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body)
    (bodySound : Boundary.StmtBoundary Γ σ body → ClosedStmtSoundness σ body) :
    ClosedFunctionBodySoundness σ body :=
  C.sound boundary bodySound

end FunctionBodyStructuralSoundnessClause

end Structural
end Soundness
end Cpp3
