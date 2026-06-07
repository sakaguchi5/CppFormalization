import CppFormalization.Cpp3.Semantics.Divergence

/-!
# CppFormalization.Cpp3.Semantics.Classification

Thin semantic classification vocabulary.

This file does not prove safety.  It only names the semantic alternatives that
later Static/Contracts/Stability/Preservation layers should rule into.
-/

namespace Cpp3
namespace Semantics

/-- A statement has a finite big-step result, including abrupt control results. -/
def StmtTerminates (σ : State) (st : CppStmt) : Prop :=
  ∃ r σ₁, BigStepStmt σ st r σ₁

/-- A block has a finite big-step result, including abrupt control results. -/
def BlockTerminates (σ : State) (ss : StmtBlock) : Prop :=
  ∃ r σ₁, BigStepBlock σ ss r σ₁

/-- A statement is semantically classified if it terminates or diverges. -/
def StmtClassified (σ : State) (st : CppStmt) : Prop :=
  StmtTerminates σ st ∨ StmtDiv σ st

/-- A block is semantically classified if it terminates or diverges. -/
def BlockClassified (σ : State) (ss : StmtBlock) : Prop :=
  BlockTerminates σ ss ∨ BlockDiv σ ss

/-- Residual stuckness: neither finite execution nor divergence is classified. -/
def StmtUnclassifiedStuck (σ : State) (st : CppStmt) : Prop :=
  ¬ StmtClassified σ st

/-- Residual block stuckness: neither finite execution nor divergence is classified. -/
def BlockUnclassifiedStuck (σ : State) (ss : StmtBlock) : Prop :=
  ¬ BlockClassified σ ss

/-- Function-body success excludes uncaught top-level break/continue. -/
inductive BigStepFunctionBody : State → CppStmt → ProgSuccess → State → Prop where
  | normal
      {σ σ₁ : State} {st : CppStmt} :
      BigStepStmt σ st .normal σ₁ →
      BigStepFunctionBody σ st .normal σ₁

  | returned
      {σ σ₁ : State} {st : CppStmt} {ov : Option Value} :
      BigStepStmt σ st (.returnResult ov) σ₁ →
      BigStepFunctionBody σ st (.returned ov) σ₁

/-- Function-body classification target: finite success or divergence. -/
def FunctionBodyClassified (σ : State) (st : CppStmt) : Prop :=
  (∃ ok σ₁, BigStepFunctionBody σ st ok σ₁) ∨ StmtDiv σ st

/-- Function-body residual stuckness: no finite success and no divergence. -/
def FunctionBodyUnclassifiedStuck (σ : State) (st : CppStmt) : Prop :=
  ¬ FunctionBodyClassified σ st

end Semantics
end Cpp3
