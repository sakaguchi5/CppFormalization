import CppFormalization.Cpp3.Boundary.Stmt
import CppFormalization.Cpp3.Semantics.Kernel.ClassificationLemmas

/-!
# CppFormalization.Cpp3.Boundary.EntryClassification

Primitive classification facts that belong to the boundary layer.

A primitive entry boundary already carries the concrete primitive semantic step.
These lemmas expose that fact without mentioning Soundness2.
-/

namespace Cpp3
namespace Boundary
namespace EntryClassification

/-- `skip` is classified by the primitive statement semantic rule. -/
theorem stmtSkip
    {Γ : TypeEnv} {σ : State}
    (_boundary : StmtBoundary Γ σ .skip) :
    Semantics.StmtClassified σ .skip := by
  exact Or.inl ⟨.normal, σ, Semantics.BigStepStmt.skip⟩

/-- Expression statements are classified directly from their runtime entry
boundary, which carries the primitive big-step. -/
theorem stmtExpr
    {Γ : TypeEnv} {σ : State} {e : CppExprStmt}
    (boundary : StmtBoundary Γ σ (.exprStmt e)) :
    Semantics.StmtClassified σ (.exprStmt e) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | exprStmt payload =>
          exact Or.inl ⟨.normal, payload.post,
            Semantics.BigStepStmt.exprStmt payload.step⟩

/-- Assignments are classified directly from their runtime entry boundary. -/
theorem stmtAssign
    {Γ : TypeEnv} {σ : State} {a : CppAssign}
    (boundary : StmtBoundary Γ σ (.assign a)) :
    Semantics.StmtClassified σ (.assign a) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | assign payload =>
          exact Or.inl ⟨.normal, payload.post,
            Semantics.BigStepStmt.assign payload.step⟩

/-- Declarations are classified directly from their runtime entry boundary. -/
theorem stmtDecl
    {Γ : TypeEnv} {σ : State} {d : CppDecl}
    (boundary : StmtBoundary Γ σ (.decl d)) :
    Semantics.StmtClassified σ (.decl d) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | decl payload =>
          exact Or.inl ⟨.normal, payload.post,
            Semantics.BigStepStmt.decl payload.step⟩

/-- Jumps are classified directly from their runtime entry boundary. -/
theorem stmtJump
    {Γ : TypeEnv} {σ : State} {j : CppJump}
    (boundary : StmtBoundary Γ σ (.jump j)) :
    Semantics.StmtClassified σ (.jump j) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | jump payload =>
          exact Or.inl ⟨payload.result, payload.post,
            Semantics.BigStepStmt.jump payload.step⟩

/-- Empty blocks are classified by the primitive block semantic rule. -/
theorem blockNil
    {Γ : TypeEnv} {σ : State}
    (_boundary : BlockBoundary Γ σ .nil) :
    Semantics.BlockClassified σ .nil := by
  exact Or.inl ⟨.normal, σ, Semantics.BigStepBlock.nil⟩

end EntryClassification
end Boundary
end Cpp3
