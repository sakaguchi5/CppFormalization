import CppFormalization.Cpp3.Soundness.Structural.Driver

/-!
# CppFormalization.Cpp3.Soundness.Primitive.Leaves

Primitive closed-fragment soundness leaves.

These proofs are the first concrete instantiation of the structural driver:
primitive statement boundaries already carry the corresponding concrete
big-step primitive step, so each primitive statement is classified by finite
statement termination.
-/

namespace Cpp3
namespace Soundness
namespace Primitive

/-- `skip` is classified by its finite normal big-step execution. -/
theorem closed_skip
    {Γ : TypeEnv} {σ : State}
    (_boundary : Boundary.StmtBoundary Γ σ .skip) :
    ClosedStmtSoundness σ .skip := by
  change Semantics.StmtClassified σ .skip
  exact Or.inl ⟨.normal, σ, Semantics.BigStepStmt.skip⟩

/-- An expression statement is classified by the primitive step carried by its boundary. -/
theorem closed_exprStmt
    {Γ : TypeEnv} {σ : State} {es : CppExprStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.exprStmt es)) :
    ClosedStmtSoundness σ (.exprStmt es) := by
  cases boundary with
  | mk _static _effect _safety entry =>
      cases entry with
      | exprStmt b =>
          change Semantics.StmtClassified σ (.exprStmt es)
          exact Or.inl ⟨.normal, b.post, Semantics.BigStepStmt.exprStmt b.step⟩

/-- An assignment is classified by the primitive step carried by its boundary. -/
theorem closed_assign
    {Γ : TypeEnv} {σ : State} {a : CppAssign}
    (boundary : Boundary.StmtBoundary Γ σ (.assign a)) :
    ClosedStmtSoundness σ (.assign a) := by
  cases boundary with
  | mk _static _effect _safety entry =>
      cases entry with
      | assign b =>
          change Semantics.StmtClassified σ (.assign a)
          exact Or.inl ⟨.normal, b.post, Semantics.BigStepStmt.assign b.step⟩

/-- A declaration is classified by the primitive step carried by its boundary. -/
theorem closed_decl
    {Γ : TypeEnv} {σ : State} {d : CppDecl}
    (boundary : Boundary.StmtBoundary Γ σ (.decl d)) :
    ClosedStmtSoundness σ (.decl d) := by
  cases boundary with
  | mk _static _effect _safety entry =>
      cases entry with
      | decl b =>
          change Semantics.StmtClassified σ (.decl d)
          exact Or.inl ⟨.normal, b.post, Semantics.BigStepStmt.decl b.step⟩

/-- A jump is classified by the primitive step carried by its boundary. -/
theorem closed_jump
    {Γ : TypeEnv} {σ : State} {j : CppJump}
    (boundary : Boundary.StmtBoundary Γ σ (.jump j)) :
    ClosedStmtSoundness σ (.jump j) := by
  cases boundary with
  | mk _static _effect _safety entry =>
      cases entry with
      | jump b =>
          change Semantics.StmtClassified σ (.jump j)
          exact Or.inl ⟨b.result, b.post, Semantics.BigStepStmt.jump b.step⟩

/-- Concrete primitive statement clauses for the closed internal fragment. -/
def primitiveStmtSoundnessClauses :
    Structural.PrimitiveStmtSoundnessClauses where
  skip := fun boundary => closed_skip boundary
  exprStmt := fun boundary => closed_exprStmt boundary
  assign := fun boundary => closed_assign boundary
  decl := fun boundary => closed_decl boundary
  jump := fun boundary => closed_jump boundary

end Primitive
end Soundness
end Cpp3
