import CppFormalization.Cpp3.Soundness2.Realize.ClassificationCompound

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationBoundary

Boundary-level classification layer for Soundness2.

`ClassificationKernel` and `ClassificationCompound` use `Source.*BoundarySource` as
public input surfaces.  That is correct at the final entry point, but too heavy
for recursive classification: seq/branch/block-tail stability gives post-state
`Boundary.*Boundary`, not a reconstructed source package with typing evidence.

This file therefore introduces boundary-level classifiers and proves the concrete
cases that are already justified by the current lower layers:

* primitive statement cases from `StmtEntryEvidence` and primitive boundaries;
* sequence normal/abrupt/divergent routing from a boundary classifier and local control;
* selected `if` branch routing from a boundary classifier and local control;
* block opening/closing from a block boundary classifier and scope-exit;
* block nil/cons routing from boundary classifiers and local control.

Source-level classifiers can then be recovered by applying `toBoundary` once at
the outer surface.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Boundary-level statement classifier.

This is the recursive core: unlike `StmtClassifierRealization`, it consumes the
runtime boundary directly.  This is the natural form for seq/branch/block-tail
continuations, because those continuations produce post-state boundaries rather
than reconstructed source packages. -/
structure BoundaryStmtClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      Boundary.StmtBoundary Γ σ st →
        Source.ClosedStmtSoundness σ st

/-- Boundary-level block classifier. -/
structure BoundaryBlockClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Boundary.BlockBoundary Γ σ body →
        Source.ClosedBlockSoundness σ body

namespace BoundaryStmtClassifierRealization

/-- Recover the existing source-level statement classifier from a boundary-level
classifier. -/
def toSourceRealization
    (K : BoundaryStmtClassifierRealization) :
    StmtClassifierRealization where
  classify := by
    intro Γ σ st source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)

/-- Recover full source-level statement cases from a boundary-level classifier. -/
def toSourceCases
    (K : BoundaryStmtClassifierRealization) :
    StmtClassificationCases where
  skip := by
    intro Γ σ source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  exprStmt := by
    intro Γ σ e source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  assign := by
    intro Γ σ a source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  decl := by
    intro Γ σ d source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  seq := by
    intro Γ σ head tail source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  ite := by
    intro Γ σ cond thenBranch elseBranch source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  whileStmt := by
    intro Γ σ cond body source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  block := by
    intro Γ σ body source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)
  jump := by
    intro Γ σ j source
    exact K.classify (Source.StmtBoundarySource.toBoundary source)

end BoundaryStmtClassifierRealization

namespace BoundaryBlockClassifierRealization

/-- Recover the existing source-level block classifier from a boundary-level
classifier. -/
def toSourceRealization
    (K : BoundaryBlockClassifierRealization) :
    BlockClassifierRealization where
  classify := by
    intro Γ σ body source
    exact K.classify (Source.BlockBoundarySource.toBoundary source)

/-- Recover full source-level block cases from a boundary-level classifier. -/
def toSourceCases
    (K : BoundaryBlockClassifierRealization) :
    BlockClassificationCases where
  nil := by
    intro Γ σ source
    exact K.classify (Source.BlockBoundarySource.toBoundary source)
  cons := by
    intro Γ σ head tail source
    exact K.classify (Source.BlockBoundarySource.toBoundary source)

end BoundaryBlockClassifierRealization

namespace BoundaryClassification

/-- `skip` is classified by the primitive statement semantic rule. -/
theorem skip
    {Γ : TypeEnv} {σ : State}
    (_boundary : Boundary.StmtBoundary Γ σ .skip) :
    Source.ClosedStmtSoundness σ .skip := by
  exact Or.inl ⟨.normal, σ, Semantics.BigStepStmt.skip⟩

/-- Expression statements are classified directly from their runtime entry
boundary, which carries the primitive big-step. -/
theorem exprStmt
    {Γ : TypeEnv} {σ : State} {e : CppExprStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.exprStmt e)) :
    Source.ClosedStmtSoundness σ (.exprStmt e) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | exprStmt payload =>
          exact Or.inl ⟨.normal, payload.post,
            Semantics.BigStepStmt.exprStmt payload.step⟩

/-- Assignments are classified directly from their runtime entry boundary. -/
theorem assign
    {Γ : TypeEnv} {σ : State} {a : CppAssign}
    (boundary : Boundary.StmtBoundary Γ σ (.assign a)) :
    Source.ClosedStmtSoundness σ (.assign a) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | assign payload =>
          exact Or.inl ⟨.normal, payload.post,
            Semantics.BigStepStmt.assign payload.step⟩

/-- Declarations are classified directly from their runtime entry boundary. -/
theorem decl
    {Γ : TypeEnv} {σ : State} {d : CppDecl}
    (boundary : Boundary.StmtBoundary Γ σ (.decl d)) :
    Source.ClosedStmtSoundness σ (.decl d) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | decl payload =>
          exact Or.inl ⟨.normal, payload.post,
            Semantics.BigStepStmt.decl payload.step⟩

/-- Jumps are classified directly from their runtime entry boundary. -/
theorem jump
    {Γ : TypeEnv} {σ : State} {j : CppJump}
    (boundary : Boundary.StmtBoundary Γ σ (.jump j)) :
    Source.ClosedStmtSoundness σ (.jump j) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | jump payload =>
          exact Or.inl ⟨payload.result, payload.post,
            Semantics.BigStepStmt.jump payload.step⟩

/-- Empty blocks are classified by the primitive block semantic rule. -/
theorem blockNil
    {Γ : TypeEnv} {σ : State}
    (_boundary : Boundary.BlockBoundary Γ σ .nil) :
    Source.ClosedBlockSoundness σ .nil := by
  exact Or.inl ⟨.normal, σ, Semantics.BigStepBlock.nil⟩

/-- Sequence classification from a boundary-level recursive classifier and the
local-control theorem that exposes the normal tail boundary. -/
theorem seq
    (stmt : BoundaryStmtClassifierRealization)
    (localControl : LocalControlRealizationTheorems)
    {Γ : TypeEnv} {σ : State} {head tail : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.seq head tail)) :
    Source.ClosedStmtSoundness σ (.seq head tail) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | seqHead headBoundary =>
          let seqBoundary : Boundary.StmtBoundary Γ σ (.seq head tail) :=
            Boundary.StmtBoundary.mk static effect safety
              (Boundary.StmtEntryEvidence.seqHead headBoundary)
          cases stmt.classify headBoundary with
          | inl headFinite =>
              rcases headFinite with ⟨r, σ₁, headStep⟩
              cases r with
              | normal =>
                  let route : Semantics.SeqNormalRoute σ σ₁ head tail :=
                    { headNormal := headStep }
                  rcases localControl.seq.source seqBoundary route with ⟨Θ, tailControl⟩
                  let stability := Source.SeqTailControlSource.toStability tailControl
                  let tailBoundary := (Stability.SeqTailStability.tailBoundary stability).tail
                  cases stmt.classify tailBoundary with
                  | inl tailFinite =>
                      rcases tailFinite with ⟨r₂, σ₂, tailStep⟩
                      exact Or.inl ⟨r₂, σ₂,
                        Semantics.BigStepStmt.seqNormal headStep tailStep⟩
                  | inr tailDiv =>
                      exact Or.inr (Semantics.StmtDiv.seqTail headStep tailDiv)
              | breakResult =>
                  exact Or.inl ⟨.breakResult, σ₁,
                    Semantics.BigStepStmt.seqBreak headStep⟩
              | continueResult =>
                  exact Or.inl ⟨.continueResult, σ₁,
                    Semantics.BigStepStmt.seqContinue headStep⟩
              | returnResult ov =>
                  exact Or.inl ⟨.returnResult ov, σ₁,
                    Semantics.BigStepStmt.seqReturn headStep⟩
          | inr headDiv =>
              exact Or.inr (Semantics.StmtDiv.seqHead headDiv)

/-- If-statement classification from a boundary-level recursive classifier and
selected-branch local control. -/
theorem ite
    (stmt : BoundaryStmtClassifierRealization)
    (localControl : LocalControlRealizationTheorems)
    {Γ : TypeEnv} {σ : State}
    {cond : CppCond} {thenBranch elseBranch : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch)) :
    Source.ClosedStmtSoundness σ (.ite cond thenBranch elseBranch) := by
  cases localControl.branch.select boundary with
  | thenSelected source =>
      let stability := Source.SelectedBranchControlSource.toStability source
      let selected := Stability.SelectedBranchStability.branchBoundary stability
      cases selected with
      | thenBoundary route condition preserved branchBoundary =>
          cases route with
          | thenRoute condStep =>
              cases stmt.classify branchBoundary with
              | inl branchFinite =>
                  rcases branchFinite with ⟨r, σ₁, branchStep⟩
                  exact Or.inl ⟨r, σ₁,
                    Semantics.BigStepStmt.iteThen condStep branchStep⟩
              | inr branchDiv =>
                  exact Or.inr (Semantics.StmtDiv.iteThen condStep branchDiv)
  | elseSelected source =>
      let stability := Source.SelectedBranchControlSource.toStability source
      let selected := Stability.SelectedBranchStability.branchBoundary stability
      cases selected with
      | elseBoundary route condition preserved branchBoundary =>
          cases route with
          | elseRoute condStep =>
              cases stmt.classify branchBoundary with
              | inl branchFinite =>
                  rcases branchFinite with ⟨r, σ₁, branchStep⟩
                  exact Or.inl ⟨r, σ₁,
                    Semantics.BigStepStmt.iteElse condStep branchStep⟩
              | inr branchDiv =>
                  exact Or.inr (Semantics.StmtDiv.iteElse condStep branchDiv)

/-- Block statement classification from an opened block boundary, a boundary-level
block classifier, and scope-close evidence. -/
theorem blockStmt
    (block : BoundaryBlockClassifierRealization)
    (scopeExit : ScopeExitRealizationTheorems)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.StmtBoundary Γ σ (.block body)) :
    Source.ClosedStmtSoundness σ (.block body) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | blockOpened openedStatic openedEffect route bodyBoundary =>
          have openedEq : _ := route.opened
          subst openedEq
          let blockBoundary : Boundary.StmtBoundary Γ σ (.block body) :=
            Boundary.StmtBoundary.mk static effect safety
              (Boundary.StmtEntryEvidence.blockOpened openedStatic openedEffect route bodyBoundary)
          cases block.classify bodyBoundary with
          | inl bodyFinite =>
              rcases bodyFinite with ⟨r, σbody, bodyStep⟩
              rcases scopeExit.blockClose.close blockBoundary bodyBoundary route bodyStep with
                ⟨Θ, Δ, σclosed, closeSource⟩
              exact Or.inl ⟨r, σclosed,
                Semantics.BigStepStmt.block bodyStep closeSource.closeStep⟩
          | inr bodyDiv =>
              exact Or.inr (Semantics.StmtDiv.block bodyDiv)

/-- Nonempty block classification from boundary-level recursive classifiers and
the local-control theorem that exposes the normal block tail boundary. -/
theorem blockCons
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization)
    (localControl : LocalControlRealizationTheorems)
    {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ (.cons head tail)) :
    Source.ClosedBlockSoundness σ (.cons head tail) := by
  cases boundary with
  | mk static effect safety entry =>
      cases entry with
      | consHead headBoundary =>
          let consBoundary : Boundary.BlockBoundary Γ σ (.cons head tail) :=
            Boundary.BlockBoundary.mk static effect safety
              (Boundary.BlockEntryEvidence.consHead headBoundary)
          cases stmt.classify headBoundary with
          | inl headFinite =>
              rcases headFinite with ⟨r, σ₁, headStep⟩
              cases r with
              | normal =>
                  let route : Semantics.BlockConsNormalRoute σ σ₁ head tail :=
                    { headNormal := headStep }
                  rcases localControl.blockTail.source consBoundary route with ⟨Θ, tailControl⟩
                  let stability := Source.BlockTailControlSource.toStability tailControl
                  let tailBoundary := (Stability.BlockTailStability.tailBoundary stability).tail
                  cases block.classify tailBoundary with
                  | inl tailFinite =>
                      rcases tailFinite with ⟨r₂, σ₂, tailStep⟩
                      exact Or.inl ⟨r₂, σ₂,
                        Semantics.BigStepBlock.consNormal headStep tailStep⟩
                  | inr tailDiv =>
                      exact Or.inr (Semantics.BlockDiv.consTail headStep tailDiv)
              | breakResult =>
                  exact Or.inl ⟨.breakResult, σ₁,
                    Semantics.BigStepBlock.consBreak headStep⟩
              | continueResult =>
                  exact Or.inl ⟨.continueResult, σ₁,
                    Semantics.BigStepBlock.consContinue headStep⟩
              | returnResult ov =>
                  exact Or.inl ⟨.returnResult ov, σ₁,
                    Semantics.BigStepBlock.consReturn headStep⟩
          | inr headDiv =>
              exact Or.inr (Semantics.BlockDiv.consHead headDiv)

end BoundaryClassification

/-- Boundary-level primitive statement case family. -/
def boundaryPrimitiveStmtCases : PrimitiveStmtClassificationCases where
  skip := by
    intro Γ σ source
    exact BoundaryClassification.skip (Source.StmtBoundarySource.toBoundary source)
  exprStmt := by
    intro Γ σ e source
    exact BoundaryClassification.exprStmt (Source.StmtBoundarySource.toBoundary source)
  assign := by
    intro Γ σ a source
    exact BoundaryClassification.assign (Source.StmtBoundarySource.toBoundary source)
  decl := by
    intro Γ σ d source
    exact BoundaryClassification.decl (Source.StmtBoundarySource.toBoundary source)
  jump := by
    intro Γ σ j source
    exact BoundaryClassification.jump (Source.StmtBoundarySource.toBoundary source)

/-- Source-level compound statement cases recovered from boundary-level recursive
classification.  The while case is supplied separately because it is already
handled by the loop-behavior layer. -/
def boundaryCompoundStmtCases
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization)
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (whileStmt :
      ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
        Source.StmtBoundarySource Γ σ (.whileStmt cond body) →
          Source.ClosedStmtSoundness σ (.whileStmt cond body)) :
    CompoundStmtClassificationCases where
  seq := by
    intro Γ σ head tail source
    exact BoundaryClassification.seq stmt localControl
      (Source.StmtBoundarySource.toBoundary source)
  ite := by
    intro Γ σ cond thenBranch elseBranch source
    exact BoundaryClassification.ite stmt localControl
      (Source.StmtBoundarySource.toBoundary source)
  whileStmt := by
    intro Γ σ cond body source
    exact whileStmt source
  block := by
    intro Γ σ body source
    exact BoundaryClassification.blockStmt block scopeExit
      (Source.StmtBoundarySource.toBoundary source)

/-- Source-level block cases recovered from boundary-level recursive
classification. -/
def boundaryBlockCases
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization)
    (localControl : LocalControlRealizationTheorems) :
    BlockCompoundClassificationCases where
  nil := by
    intro Γ σ source
    exact BoundaryClassification.blockNil (Source.BlockBoundarySource.toBoundary source)
  cons := by
    intro Γ σ head tail source
    exact BoundaryClassification.blockCons stmt block localControl
      (Source.BlockBoundarySource.toBoundary source)

end Realize
end Soundness2
end Cpp3
