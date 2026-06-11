import CppFormalization.Cpp3.Semantics.Kernel.Classification

/-!
# CppFormalization.Cpp3.Semantics.Kernel.ClassificationLemmas

Bottom-up semantic classification lemmas.

These lemmas are purely semantic: they combine already obtained finite/divergent
classifications through the big-step routing rules.  They do not mention
Soundness2, boundaries, typing, safety, or stability.
-/

namespace Cpp3
namespace Semantics

/-- Finite statement execution classifies a statement. -/
theorem stmtClassified_of_terminates
    {σ : State} {st : CppStmt}
    (h : StmtTerminates σ st) :
    StmtClassified σ st :=
  Or.inl h

/-- Statement divergence classifies a statement. -/
theorem stmtClassified_of_div
    {σ : State} {st : CppStmt}
    (h : StmtDiv σ st) :
    StmtClassified σ st :=
  Or.inr h

/-- Finite block execution classifies a block body. -/
theorem blockClassified_of_terminates
    {σ : State} {body : StmtBlock}
    (h : BlockTerminates σ body) :
    BlockClassified σ body :=
  Or.inl h

/-- Block divergence classifies a block body. -/
theorem blockClassified_of_div
    {σ : State} {body : StmtBlock}
    (h : BlockDiv σ body) :
    BlockClassified σ body :=
  Or.inr h

/-- Function-body finite success classifies a function body. -/
theorem functionBodyClassified_of_success
    {σ : State} {body : CppStmt}
    (h : ∃ ok σ₁, BigStepFunctionBody σ body ok σ₁) :
    FunctionBodyClassified σ body :=
  Or.inl h

/-- Function-body divergence classifies a function body. -/
theorem functionBodyClassified_of_div
    {σ : State} {body : CppStmt}
    (h : StmtDiv σ body) :
    FunctionBodyClassified σ body :=
  Or.inr h

/-- A classified statement is not residually unclassified-stuck. -/
theorem not_stmtUnclassifiedStuck_of_classified
    {σ : State} {st : CppStmt}
    (h : StmtClassified σ st) :
    ¬ StmtUnclassifiedStuck σ st := by
  intro hstuck
  exact hstuck h

/-- A classified block body is not residually unclassified-stuck. -/
theorem not_blockUnclassifiedStuck_of_classified
    {σ : State} {body : StmtBlock}
    (h : BlockClassified σ body) :
    ¬ BlockUnclassifiedStuck σ body := by
  intro hstuck
  exact hstuck h

/-- A classified function body is not residually unclassified-stuck. -/
theorem not_functionBodyUnclassifiedStuck_of_classified
    {σ : State} {body : CppStmt}
    (h : FunctionBodyClassified σ body) :
    ¬ FunctionBodyUnclassifiedStuck σ body := by
  intro hstuck
  exact hstuck h

/-- Semantic classification of a sequence from head classification and the tail
classification available after a normal head result. -/
theorem stmtClassified_seq
    {σ : State} {head tail : CppStmt}
    (headClassified : StmtClassified σ head)
    (tailClassifiedOfNormal :
      ∀ {σ₁ : State},
        BigStepStmt σ head .normal σ₁ →
          StmtClassified σ₁ tail) :
    StmtClassified σ (.seq head tail) := by
  cases headClassified with
  | inl headFinite =>
      rcases headFinite with ⟨r, σ₁, headStep⟩
      cases r with
      | normal =>
          cases tailClassifiedOfNormal headStep with
          | inl tailFinite =>
              rcases tailFinite with ⟨r₂, σ₂, tailStep⟩
              exact Or.inl ⟨r₂, σ₂,
                BigStepStmt.seqNormal headStep tailStep⟩
          | inr tailDiv =>
              exact Or.inr (StmtDiv.seqTail headStep tailDiv)
      | breakResult =>
          exact Or.inl ⟨.breakResult, σ₁,
            BigStepStmt.seqBreak headStep⟩
      | continueResult =>
          exact Or.inl ⟨.continueResult, σ₁,
            BigStepStmt.seqContinue headStep⟩
      | returnResult ov =>
          exact Or.inl ⟨.returnResult ov, σ₁,
            BigStepStmt.seqReturn headStep⟩
  | inr headDiv =>
      exact Or.inr (StmtDiv.seqHead headDiv)

/-- Semantic classification of an if-statement through the selected then branch. -/
theorem stmtClassified_iteThen
    {σ σc : State} {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (condStep : BigStepCond σ cond true σc)
    (branchClassified : StmtClassified σc thenBranch) :
    StmtClassified σ (.ite cond thenBranch elseBranch) := by
  cases branchClassified with
  | inl branchFinite =>
      rcases branchFinite with ⟨r, σ₁, branchStep⟩
      exact Or.inl ⟨r, σ₁,
        BigStepStmt.iteThen condStep branchStep⟩
  | inr branchDiv =>
      exact Or.inr (StmtDiv.iteThen condStep branchDiv)

/-- Semantic classification of an if-statement through the selected else branch. -/
theorem stmtClassified_iteElse
    {σ σc : State} {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (condStep : BigStepCond σ cond false σc)
    (branchClassified : StmtClassified σc elseBranch) :
    StmtClassified σ (.ite cond thenBranch elseBranch) := by
  cases branchClassified with
  | inl branchFinite =>
      rcases branchFinite with ⟨r, σ₁, branchStep⟩
      exact Or.inl ⟨r, σ₁,
        BigStepStmt.iteElse condStep branchStep⟩
  | inr branchDiv =>
      exact Or.inr (StmtDiv.iteElse condStep branchDiv)

/-- Semantic classification of a block statement from classification of the opened
block body plus a close step for every finite body result. -/
theorem stmtClassified_block
    {σ : State} {body : StmtBlock}
    (bodyClassified : BlockClassified (pushScope σ) body)
    (closeOfFinite :
      ∀ {r : CtrlResult} {σbody : State},
        BigStepBlock (pushScope σ) body r σbody →
          ∃ σclosed : State, popScope? σbody = some σclosed) :
    StmtClassified σ (.block body) := by
  cases bodyClassified with
  | inl bodyFinite =>
      rcases bodyFinite with ⟨r, σbody, bodyStep⟩
      rcases closeOfFinite bodyStep with ⟨σclosed, closeStep⟩
      exact Or.inl ⟨r, σclosed,
        BigStepStmt.block bodyStep closeStep⟩
  | inr bodyDiv =>
      exact Or.inr (StmtDiv.block bodyDiv)

/-- Semantic classification of a nonempty block body from head classification and
the tail classification available after a normal head result. -/
theorem blockClassified_cons
    {σ : State} {head : CppStmt} {tail : StmtBlock}
    (headClassified : StmtClassified σ head)
    (tailClassifiedOfNormal :
      ∀ {σ₁ : State},
        BigStepStmt σ head .normal σ₁ →
          BlockClassified σ₁ tail) :
    BlockClassified σ (.cons head tail) := by
  cases headClassified with
  | inl headFinite =>
      rcases headFinite with ⟨r, σ₁, headStep⟩
      cases r with
      | normal =>
          cases tailClassifiedOfNormal headStep with
          | inl tailFinite =>
              rcases tailFinite with ⟨r₂, σ₂, tailStep⟩
              exact Or.inl ⟨r₂, σ₂,
                BigStepBlock.consNormal headStep tailStep⟩
          | inr tailDiv =>
              exact Or.inr (BlockDiv.consTail headStep tailDiv)
      | breakResult =>
          exact Or.inl ⟨.breakResult, σ₁,
            BigStepBlock.consBreak headStep⟩
      | continueResult =>
          exact Or.inl ⟨.continueResult, σ₁,
            BigStepBlock.consContinue headStep⟩
      | returnResult ov =>
          exact Or.inl ⟨.returnResult ov, σ₁,
            BigStepBlock.consReturn headStep⟩
  | inr headDiv =>
      exact Or.inr (BlockDiv.consHead headDiv)

/-- Lift statement classification to function-body classification once uncaught
finite top-level `break` and `continue` results are known impossible. -/
theorem functionBodyClassified_of_stmtClassified
    {σ : State} {body : CppStmt}
    (stmtClassified : StmtClassified σ body)
    (noBreak :
      ∀ {σ₁ : State},
        BigStepStmt σ body .breakResult σ₁ → False)
    (noContinue :
      ∀ {σ₁ : State},
        BigStepStmt σ body .continueResult σ₁ → False) :
    FunctionBodyClassified σ body := by
  cases stmtClassified with
  | inl finite =>
      rcases finite with ⟨r, σ₁, step⟩
      cases r with
      | normal =>
          exact Or.inl ⟨.normal, σ₁,
            BigStepFunctionBody.normal step⟩
      | breakResult =>
          exact False.elim (noBreak step)
      | continueResult =>
          exact False.elim (noContinue step)
      | returnResult ov =>
          exact Or.inl ⟨.returned ov, σ₁,
            BigStepFunctionBody.returned step⟩
  | inr div =>
      exact Or.inr div

end Semantics
end Cpp3
