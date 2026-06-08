import CppFormalization.Cpp3.Soundness.Bridge

/-!
# CppFormalization.Cpp3.Soundness.Structural.Primitive

Primitive structural soundness surfaces for the closed internal C++ fragment.

This file is the first part of the real Soundness layer: it fixes the
statement/block/function-body targets that later constructor-local proofs must
produce.  It still does not unfold the operational semantics of primitive
statements; instead it names the primitive proof obligations in the same
closed-fragment target used by `Soundness.Target`.
-/

namespace Cpp3
namespace Soundness
namespace Structural

/-- Statement structural soundness at a concrete entry boundary. -/
abbrev StmtStructuralSoundness
    (Γ : TypeEnv) (σ : State) (st : CppStmt) : Prop :=
  Boundary.StmtBoundary Γ σ st → ClosedStmtSoundness σ st

/-- Block-body structural soundness at a concrete entry boundary. -/
abbrev BlockStructuralSoundness
    (Γ : TypeEnv) (σ : State) (body : StmtBlock) : Prop :=
  Boundary.BlockBoundary Γ σ body → ClosedBlockSoundness σ body

/-- Function-body structural soundness at a concrete entry boundary. -/
abbrev FunctionBodyStructuralSoundness
    (Γ : TypeEnv) (σ : State) (body : CppStmt) : Prop :=
  Boundary.FunctionBodyBoundary Γ σ body → ClosedFunctionBodySoundness σ body

/-- A statement structural soundness proof rules out residual statement stuckness. -/
theorem noStmtUnclassifiedStuck_of_stmtStructuralSoundness
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (h : StmtStructuralSoundness Γ σ st)
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_of_closedStmtSoundness (h boundary)

/-- A block structural soundness proof rules out residual block stuckness. -/
theorem noBlockUnclassifiedStuck_of_blockStructuralSoundness
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (h : BlockStructuralSoundness Γ σ body)
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_of_closedBlockSoundness (h boundary)

/-- A function-body structural soundness proof rules out residual function-body stuckness. -/
theorem noFunctionBodyUnclassifiedStuck_of_functionBodyStructuralSoundness
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (h : FunctionBodyStructuralSoundness Γ σ body)
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_of_closedFunctionBodySoundness (h boundary)

/-- Constructor-local closed soundness obligations for primitive statements.

These are the primitive leaves of the structural proof.  Later files should
instantiate them from the actual primitive operational semantics and the
corresponding Boundary/SafetyFragment evidence. -/
structure PrimitiveStmtSoundnessClauses : Type where
  skip :
    ∀ {Γ : TypeEnv} {σ : State},
      StmtStructuralSoundness Γ σ .skip
  exprStmt :
    ∀ {Γ : TypeEnv} {σ : State} {es : CppExprStmt},
      StmtStructuralSoundness Γ σ (.exprStmt es)
  assign :
    ∀ {Γ : TypeEnv} {σ : State} {a : CppAssign},
      StmtStructuralSoundness Γ σ (.assign a)
  decl :
    ∀ {Γ : TypeEnv} {σ : State} {d : CppDecl},
      StmtStructuralSoundness Γ σ (.decl d)
  jump :
    ∀ {Γ : TypeEnv} {σ : State} {j : CppJump},
      StmtStructuralSoundness Γ σ (.jump j)

namespace PrimitiveStmtSoundnessClauses

/-- Apply the primitive skip soundness clause. -/
theorem closed_skip
    (C : PrimitiveStmtSoundnessClauses)
    {Γ : TypeEnv} {σ : State}
    (boundary : Boundary.StmtBoundary Γ σ .skip) :
    ClosedStmtSoundness σ .skip :=
  C.skip boundary

/-- Apply the primitive expression-statement soundness clause. -/
theorem closed_exprStmt
    (C : PrimitiveStmtSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {es : CppExprStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.exprStmt es)) :
    ClosedStmtSoundness σ (.exprStmt es) :=
  C.exprStmt boundary

/-- Apply the primitive assignment soundness clause. -/
theorem closed_assign
    (C : PrimitiveStmtSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {a : CppAssign}
    (boundary : Boundary.StmtBoundary Γ σ (.assign a)) :
    ClosedStmtSoundness σ (.assign a) :=
  C.assign boundary

/-- Apply the primitive declaration soundness clause. -/
theorem closed_decl
    (C : PrimitiveStmtSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {d : CppDecl}
    (boundary : Boundary.StmtBoundary Γ σ (.decl d)) :
    ClosedStmtSoundness σ (.decl d) :=
  C.decl boundary

/-- Apply the primitive jump soundness clause. -/
theorem closed_jump
    (C : PrimitiveStmtSoundnessClauses)
    {Γ : TypeEnv} {σ : State} {j : CppJump}
    (boundary : Boundary.StmtBoundary Γ σ (.jump j)) :
    ClosedStmtSoundness σ (.jump j) :=
  C.jump boundary

end PrimitiveStmtSoundnessClauses

end Structural
end Soundness
end Cpp3
