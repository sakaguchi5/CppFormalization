import CppFormalization.Cpp3.Soundness.Primitive.Leaves

/-!
# CppFormalization.Cpp3.Soundness.Semantic.Seq

Pure semantic propagation lemmas for statement sequencing.
-/

namespace Cpp3
namespace Soundness
namespace Semantic

/-- Classify `head; tail` from a classified head and classified normal-head tails. -/
theorem seq_of_classified_head
    {σ : State} {head tail : CppStmt}
    (headSound : ClosedStmtSoundness σ head)
    (tailSound :
      ∀ {σ₁ : State},
        Semantics.SeqNormalRoute σ σ₁ head tail →
          ClosedStmtSoundness σ₁ tail) :
    ClosedStmtSoundness σ (.seq head tail) := by
  change Semantics.StmtClassified σ (.seq head tail)
  change Semantics.StmtClassified σ head at headSound
  cases headSound with
  | inr headDiv =>
      exact Or.inr (Semantics.StmtDiv.seqHead headDiv)
  | inl headTerm =>
      rcases headTerm with ⟨r, σ₁, headStep⟩
      cases r with
      | normal =>
          have tailClassified : ClosedStmtSoundness σ₁ tail :=
            tailSound ⟨headStep⟩
          change Semantics.StmtClassified σ₁ tail at tailClassified
          cases tailClassified with
          | inr tailDiv =>
              exact Or.inr (Semantics.StmtDiv.seqTail headStep tailDiv)
          | inl tailTerm =>
              rcases tailTerm with ⟨r₂, σ₂, tailStep⟩
              exact Or.inl ⟨r₂, σ₂,
                Semantics.BigStepStmt.seqNormal headStep tailStep⟩
      | breakResult =>
          exact Or.inl ⟨.breakResult, σ₁,
            Semantics.BigStepStmt.seqBreak headStep⟩
      | continueResult =>
          exact Or.inl ⟨.continueResult, σ₁,
            Semantics.BigStepStmt.seqContinue headStep⟩
      | returnResult ov =>
          exact Or.inl ⟨.returnResult ov, σ₁,
            Semantics.BigStepStmt.seqReturn headStep⟩

end Semantic
end Soundness
end Cpp3
