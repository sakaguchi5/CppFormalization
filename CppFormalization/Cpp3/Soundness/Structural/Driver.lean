import CppFormalization.Cpp3.Soundness.Structural.Compound

/-!
# CppFormalization.Cpp3.Soundness.Structural.Driver

The structural soundness driver for the closed internal C++ fragment.

This file gathers the constructor-local clauses into one package.  It is the
first "body" layer above the target/bridge files: the remaining work is to
instantiate these clauses from the concrete Semantics/Boundary/Stability facts.
-/

namespace Cpp3
namespace Soundness
namespace Structural

/-- Statement constructor clauses for closed structural soundness. -/
structure StmtStructuralSoundnessClauses : Type where
  primitive : PrimitiveStmtSoundnessClauses
  seq : SeqStructuralSoundnessClause
  branch : BranchStructuralSoundnessClause
  whileStmt : WhileStructuralSoundnessClause
  blockStmt : BlockStmtStructuralSoundnessClause

/-- Block-body constructor clauses for closed structural soundness. -/
structure BlockStructuralSoundnessClauses : Type where
  nil : BlockNilStructuralSoundnessClause
  cons : BlockConsStructuralSoundnessClause

/-- Function-body constructor clauses for closed structural soundness. -/
structure FunctionBodyStructuralSoundnessClauses : Type where
  body : FunctionBodyStructuralSoundnessClause

/-- Complete structural soundness driver for the closed internal C++ fragment.

The package is intentionally clause-oriented rather than axiom-oriented: each
field is a visible constructor-local obligation that later proof files must
instantiate. -/
structure ClosedStructuralSoundnessDriver : Type where
  stmt : StmtStructuralSoundnessClauses
  block : BlockStructuralSoundnessClauses
  functionBody : FunctionBodyStructuralSoundnessClauses

namespace StmtStructuralSoundnessClauses

/-- Apply the primitive skip clause from a statement clause package. -/
theorem closed_skip
    (C : StmtStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State}
    (boundary : Boundary.StmtBoundary Γ σ .skip) :
    ClosedStmtSoundness σ .skip :=
  C.primitive.skip boundary

/-- Apply the primitive expression-statement clause from a statement clause package. -/
theorem closed_exprStmt
    (C : StmtStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {es : CppExprStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.exprStmt es)) :
    ClosedStmtSoundness σ (.exprStmt es) :=
  C.primitive.exprStmt boundary

/-- Apply the primitive assignment clause from a statement clause package. -/
theorem closed_assign
    (C : StmtStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {a : CppAssign}
    (boundary : Boundary.StmtBoundary Γ σ (.assign a)) :
    ClosedStmtSoundness σ (.assign a) :=
  C.primitive.assign boundary

/-- Apply the primitive declaration clause from a statement clause package. -/
theorem closed_decl
    (C : StmtStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {d : CppDecl}
    (boundary : Boundary.StmtBoundary Γ σ (.decl d)) :
    ClosedStmtSoundness σ (.decl d) :=
  C.primitive.decl boundary

/-- Apply the primitive jump clause from a statement clause package. -/
theorem closed_jump
    (C : StmtStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {j : CppJump}
    (boundary : Boundary.StmtBoundary Γ σ (.jump j)) :
    ClosedStmtSoundness σ (.jump j) :=
  C.primitive.jump boundary

/-- Apply the sequence clause from a statement clause package. -/
theorem closed_seq
    (C : StmtStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {head tail : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.seq head tail))
    (headSound : ClosedStmtSoundness σ head)
    (tailSound :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        Continuation.SeqTailContinuation Γ Θ σ σ₁ head tail →
          ClosedStmtSoundness σ₁ tail) :
    ClosedStmtSoundness σ (.seq head tail) :=
  C.seq.sound boundary headSound tailSound

/-- Apply the branch clause from a statement clause package. -/
theorem closed_ite
    (C : StmtStructuralSoundnessClauses)
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
  C.branch.sound boundary thenSound elseSound

/-- Apply the while clause from a statement clause package. -/
theorem closed_while
    (C : StmtStructuralSoundnessClauses)
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
  C.whileStmt.sound boundary bodySound reentrySound

/-- Apply the block-statement clause from a statement clause package. -/
theorem closed_block
    (C : StmtStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.StmtBoundary Γ σ (.block body))
    (bodySound :
      ∀ {Γopen : TypeEnv} {σopened : State},
        Boundary.BlockBoundary Γopen σopened body →
          ClosedBlockSoundness σopened body) :
    ClosedStmtSoundness σ (.block body) :=
  C.blockStmt.sound boundary bodySound

end StmtStructuralSoundnessClauses

namespace BlockStructuralSoundnessClauses

/-- Apply the empty-block clause from a block clause package. -/
theorem closed_nil
    (C : BlockStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State}
    (boundary : Boundary.BlockBoundary Γ σ .nil) :
    ClosedBlockSoundness σ .nil :=
  C.nil.sound boundary

/-- Apply the block-cons clause from a block clause package. -/
theorem closed_cons
    (C : BlockStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ (.cons head tail))
    (headSound : ClosedStmtSoundness σ head)
    (tailSound :
      ∀ {Θ : TypeEnv} {σ₁ : State},
        Continuation.BlockTailContinuation Γ Θ σ σ₁ head tail →
          ClosedBlockSoundness σ₁ tail) :
    ClosedBlockSoundness σ (.cons head tail) :=
  C.cons.sound boundary headSound tailSound

end BlockStructuralSoundnessClauses

namespace FunctionBodyStructuralSoundnessClauses

/-- Apply the function-body clause from a function-body clause package. -/
theorem closed_body
    (C : FunctionBodyStructuralSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body)
    (bodySound : Boundary.StmtBoundary Γ σ body → ClosedFunctionBodySoundness σ body) :
    ClosedFunctionBodySoundness σ body :=
  C.body.sound boundary bodySound

end FunctionBodyStructuralSoundnessClauses

namespace ClosedStructuralSoundnessDriver

/-- Extract the statement constructor clauses from the structural driver. -/
def stmtClauses (D : ClosedStructuralSoundnessDriver) : StmtStructuralSoundnessClauses :=
  D.stmt

/-- Extract the block constructor clauses from the structural driver. -/
def blockClauses (D : ClosedStructuralSoundnessDriver) : BlockStructuralSoundnessClauses :=
  D.block

/-- Extract the function-body constructor clauses from the structural driver. -/
def functionBodyClauses
    (D : ClosedStructuralSoundnessDriver) : FunctionBodyStructuralSoundnessClauses :=
  D.functionBody

end ClosedStructuralSoundnessDriver

end Structural
end Soundness
end Cpp3
