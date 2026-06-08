import CppFormalization.Cpp3.Soundness.Semantic.Seq

/-!
# CppFormalization.Cpp3.Soundness.Semantic.Block

Pure semantic propagation lemmas for block bodies and block statements.
-/

namespace Cpp3
namespace Soundness
namespace Semantic

/-- The empty block body is classified by its finite normal execution. -/
theorem block_nil :
    {Γ : TypeEnv} → {σ : State} →
    Boundary.BlockBoundary Γ σ .nil →
      ClosedBlockSoundness σ .nil := by
  intro _Γ σ _boundary
  change Semantics.BlockClassified σ .nil
  exact Or.inl ⟨.normal, σ, Semantics.BigStepBlock.nil⟩

/-- Classify a block cons from a classified head and classified normal-head tails. -/
theorem block_cons_of_classified_head
    {σ : State} {head : CppStmt} {tail : StmtBlock}
    (headSound : ClosedStmtSoundness σ head)
    (tailSound :
      ∀ {σ₁ : State},
        Semantics.BlockConsNormalRoute σ σ₁ head tail →
          ClosedBlockSoundness σ₁ tail) :
    ClosedBlockSoundness σ (.cons head tail) := by
  change Semantics.BlockClassified σ (.cons head tail)
  change Semantics.StmtClassified σ head at headSound
  cases headSound with
  | inr headDiv =>
      exact Or.inr (Semantics.BlockDiv.consHead headDiv)
  | inl headTerm =>
      rcases headTerm with ⟨r, σ₁, headStep⟩
      cases r with
      | normal =>
          have tailClassified : ClosedBlockSoundness σ₁ tail :=
            tailSound ⟨headStep⟩
          change Semantics.BlockClassified σ₁ tail at tailClassified
          cases tailClassified with
          | inr tailDiv =>
              exact Or.inr (Semantics.BlockDiv.consTail headStep tailDiv)
          | inl tailTerm =>
              rcases tailTerm with ⟨r₂, σ₂, tailStep⟩
              exact Or.inl ⟨r₂, σ₂,
                Semantics.BigStepBlock.consNormal headStep tailStep⟩
      | breakResult =>
          exact Or.inl ⟨.breakResult, σ₁,
            Semantics.BigStepBlock.consBreak headStep⟩
      | continueResult =>
          exact Or.inl ⟨.continueResult, σ₁,
            Semantics.BigStepBlock.consContinue headStep⟩
      | returnResult ov =>
          exact Or.inl ⟨.returnResult ov, σ₁,
            Semantics.BigStepBlock.consReturn headStep⟩

/-- Lift an opened block-body classification through the block-statement semantics. -/
theorem block_stmt_of_opened_body
    {σ σopened : State} {body : StmtBlock}
    (route : Semantics.OpenedBlockRoute σ σopened body)
    (bodySound : ClosedBlockSoundness σopened body)
    (close :
      ∀ {r : CtrlResult} {σbody : State},
        Semantics.BigStepBlock σopened body r σbody →
          ∃ σclosed : State, popScope? σbody = some σclosed) :
    ClosedStmtSoundness σ (.block body) := by
  cases route with
  | mk opened =>
      cases opened
      change Semantics.StmtClassified σ (.block body)
      change Semantics.BlockClassified (pushScope σ) body at bodySound
      cases bodySound with
      | inr bodyDiv =>
          exact Or.inr (Semantics.StmtDiv.block bodyDiv)
      | inl bodyTerm =>
          rcases bodyTerm with ⟨r, σbody, bodyStep⟩
          rcases close bodyStep with ⟨σclosed, closeStep⟩
          exact Or.inl ⟨r, σclosed,
            Semantics.BigStepStmt.block bodyStep closeStep⟩

end Semantic
end Soundness
end Cpp3
