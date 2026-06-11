import CppFormalization.Cpp3.Soundness2.Realize.LocalControl
import CppFormalization.Cpp3.Soundness2.Realize.ScopeExit
import CppFormalization.Cpp3.Soundness2.Realize.LoopBehavior
import CppFormalization.Cpp3.Soundness2.Source.ClosedInternal
import CppFormalization.Cpp3.Boundary.EntryClassification

/-!
# CppFormalization.Cpp3.Soundness2.Realize.ClassificationBoundary

Boundary-level statement/block classifier layer.

This file is the C++-semantic heart of the Realize route.  It restores the
concrete boundary-level classification cases: primitive statements classify from
entry evidence; seq/block-tail continue through local control; branch selection
uses local control; block statements use scope exit; while statements use loop
behavior.
-/

namespace Cpp3
namespace Soundness2
namespace Realize

/-- Source-level realized classifier for closed-internal statements. -/
structure StmtClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {st : CppStmt},
      Source.StmtBoundarySource Γ σ st →
        Source.ClosedStmtSoundness σ st

/-- Source-level realized classifier for closed-internal block bodies. -/
structure BlockClassifierRealization : Type where
  classify :
    ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
      Source.BlockBoundarySource Γ σ body →
        Source.ClosedBlockSoundness σ body

/-- Boundary-level statement classifier.

This is the recursive core consumed after local-control handoffs. -/
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

/-- Boundary-level statement and block classifiers constructed together. -/
structure BoundaryClassifierRealization : Type where
  stmt : BoundaryStmtClassifierRealization
  block : BoundaryBlockClassifierRealization

namespace BoundaryStmtClassifierRealization

/-- Recover the source-level statement classifier from the boundary-level core. -/
def toSourceRealization
    (K : BoundaryStmtClassifierRealization) :
    StmtClassifierRealization where
  classify := by
    intro Γ σ st source
    exact K.classify source.toBoundary

end BoundaryStmtClassifierRealization

namespace BoundaryBlockClassifierRealization

/-- Recover the source-level block classifier from the boundary-level core. -/
def toSourceRealization
    (K : BoundaryBlockClassifierRealization) :
    BlockClassifierRealization where
  classify := by
    intro Γ σ body source
    exact K.classify source.toBoundary

end BoundaryBlockClassifierRealization

namespace BoundaryClassification

/-- `skip` is classified by the lower primitive boundary-entry theorem. -/
theorem skip
    {Γ : TypeEnv} {σ : State}
    (boundary : Boundary.StmtBoundary Γ σ .skip) :
    Source.ClosedStmtSoundness σ .skip :=
  Boundary.EntryClassification.stmtSkip boundary

/-- Expression statements are classified by the lower primitive boundary-entry theorem. -/
theorem exprStmt
    {Γ : TypeEnv} {σ : State} {e : CppExprStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.exprStmt e)) :
    Source.ClosedStmtSoundness σ (.exprStmt e) :=
  Boundary.EntryClassification.stmtExpr boundary

/-- Assignments are classified by the lower primitive boundary-entry theorem. -/
theorem assign
    {Γ : TypeEnv} {σ : State} {a : CppAssign}
    (boundary : Boundary.StmtBoundary Γ σ (.assign a)) :
    Source.ClosedStmtSoundness σ (.assign a) :=
  Boundary.EntryClassification.stmtAssign boundary

/-- Declarations are classified by the lower primitive boundary-entry theorem. -/
theorem decl
    {Γ : TypeEnv} {σ : State} {d : CppDecl}
    (boundary : Boundary.StmtBoundary Γ σ (.decl d)) :
    Source.ClosedStmtSoundness σ (.decl d) :=
  Boundary.EntryClassification.stmtDecl boundary

/-- Jumps are classified by the lower primitive boundary-entry theorem. -/
theorem jump
    {Γ : TypeEnv} {σ : State} {j : CppJump}
    (boundary : Boundary.StmtBoundary Γ σ (.jump j)) :
    Source.ClosedStmtSoundness σ (.jump j) :=
  Boundary.EntryClassification.stmtJump boundary

/-- Empty blocks are classified by the lower primitive boundary-entry theorem. -/
theorem blockNil
    {Γ : TypeEnv} {σ : State}
    (boundary : Boundary.BlockBoundary Γ σ .nil) :
    Source.ClosedBlockSoundness σ .nil :=
  Boundary.EntryClassification.blockNil boundary

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
          exact
            Semantics.stmtClassified_seq
              (stmt.classify headBoundary)
              (by
                intro σ₁ headStep
                let seqBoundary : Boundary.StmtBoundary Γ σ (.seq head tail) :=
                  Boundary.StmtBoundary.mk static effect safety
                    (Boundary.StmtEntryEvidence.seqHead headBoundary)
                let route : Semantics.SeqNormalRoute σ σ₁ head tail :=
                  { headNormal := headStep }
                rcases localControl.seq.source seqBoundary route with ⟨Θ, tailControl⟩
                let stability := Source.SeqTailControlSource.toStability tailControl
                let tailBoundary := (Stability.SeqTailStability.tailBoundary stability).tail
                exact stmt.classify tailBoundary)

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
              exact Semantics.stmtClassified_iteThen condStep
                (stmt.classify branchBoundary)
  | elseSelected source =>
      let stability := Source.SelectedBranchControlSource.toStability source
      let selected := Stability.SelectedBranchStability.branchBoundary stability
      cases selected with
      | elseBoundary route condition preserved branchBoundary =>
          cases route with
          | elseRoute condStep =>
              exact Semantics.stmtClassified_iteElse condStep
                (stmt.classify branchBoundary)

/-- While-statement classification from the loop-behavior theorem. -/
theorem whileStmt
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ (.whileStmt cond body)) :
    Source.ClosedStmtSoundness σ (.whileStmt cond body) := by
  rcases loopBehavior.certify boundary with ⟨Γc, cert⟩
  exact cert.closedWhileSoundness

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
          exact
            Semantics.stmtClassified_block
              (block.classify bodyBoundary)
              (by
                intro r σbody bodyStep
                rcases scopeExit.blockClose.close blockBoundary bodyBoundary route bodyStep with
                  ⟨Θ, Δ, σclosed, closeSource⟩
                exact ⟨σclosed, closeSource.closeStep⟩)

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
          exact
            Semantics.blockClassified_cons
              (stmt.classify headBoundary)
              (by
                intro σ₁ headStep
                let consBoundary : Boundary.BlockBoundary Γ σ (.cons head tail) :=
                  Boundary.BlockBoundary.mk static effect safety
                    (Boundary.BlockEntryEvidence.consHead headBoundary)
                let route : Semantics.BlockConsNormalRoute σ σ₁ head tail :=
                  { headNormal := headStep }
                rcases localControl.blockTail.source consBoundary route with ⟨Θ, tailControl⟩
                let stability := Source.BlockTailControlSource.toStability tailControl
                let tailBoundary := (Stability.BlockTailStability.tailBoundary stability).tail
                exact block.classify tailBoundary)

end BoundaryClassification

/-- A statement classifier built from constructor cases.  This is a useful honest
interface for external or future recursive construction proofs. -/
structure BoundaryStmtClassificationCases : Type where
  skip : ∀ {Γ : TypeEnv} {σ : State},
    Boundary.StmtBoundary Γ σ .skip → Source.ClosedStmtSoundness σ .skip
  exprStmt : ∀ {Γ : TypeEnv} {σ : State} {e : CppExprStmt},
    Boundary.StmtBoundary Γ σ (.exprStmt e) → Source.ClosedStmtSoundness σ (.exprStmt e)
  assign : ∀ {Γ : TypeEnv} {σ : State} {a : CppAssign},
    Boundary.StmtBoundary Γ σ (.assign a) → Source.ClosedStmtSoundness σ (.assign a)
  decl : ∀ {Γ : TypeEnv} {σ : State} {d : CppDecl},
    Boundary.StmtBoundary Γ σ (.decl d) → Source.ClosedStmtSoundness σ (.decl d)
  seq : ∀ {Γ : TypeEnv} {σ : State} {head tail : CppStmt},
    Boundary.StmtBoundary Γ σ (.seq head tail) → Source.ClosedStmtSoundness σ (.seq head tail)
  ite : ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {thenBranch elseBranch : CppStmt},
    Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
      Source.ClosedStmtSoundness σ (.ite cond thenBranch elseBranch)
  whileStmt : ∀ {Γ : TypeEnv} {σ : State} {cond : CppCond} {body : CppStmt},
    Boundary.StmtBoundary Γ σ (.whileStmt cond body) →
      Source.ClosedStmtSoundness σ (.whileStmt cond body)
  block : ∀ {Γ : TypeEnv} {σ : State} {body : StmtBlock},
    Boundary.StmtBoundary Γ σ (.block body) → Source.ClosedStmtSoundness σ (.block body)
  jump : ∀ {Γ : TypeEnv} {σ : State} {j : CppJump},
    Boundary.StmtBoundary Γ σ (.jump j) → Source.ClosedStmtSoundness σ (.jump j)

namespace BoundaryStmtClassificationCases

/-- Dispatch boundary statement cases. -/
def toClassifier
    (K : BoundaryStmtClassificationCases) :
    BoundaryStmtClassifierRealization where
  classify := by
    intro Γ σ st boundary
    cases st with
    | skip => exact K.skip boundary
    | exprStmt e => exact K.exprStmt boundary
    | assign a => exact K.assign boundary
    | decl d => exact K.decl boundary
    | seq head tail => exact K.seq boundary
    | ite cond thenBranch elseBranch => exact K.ite boundary
    | whileStmt cond body => exact K.whileStmt boundary
    | block body => exact K.block boundary
    | jump j => exact K.jump boundary

end BoundaryStmtClassificationCases

/-- A block classifier built from constructor cases. -/
structure BoundaryBlockClassificationCases : Type where
  nil : ∀ {Γ : TypeEnv} {σ : State},
    Boundary.BlockBoundary Γ σ .nil → Source.ClosedBlockSoundness σ .nil
  cons : ∀ {Γ : TypeEnv} {σ : State} {head : CppStmt} {tail : StmtBlock},
    Boundary.BlockBoundary Γ σ (.cons head tail) → Source.ClosedBlockSoundness σ (.cons head tail)

namespace BoundaryBlockClassificationCases

/-- Dispatch boundary block cases. -/
def toClassifier
    (K : BoundaryBlockClassificationCases) :
    BoundaryBlockClassifierRealization where
  classify := by
    intro Γ σ body boundary
    cases body with
    | nil => exact K.nil boundary
    | cons head tail => exact K.cons boundary

end BoundaryBlockClassificationCases

/-- Build the boundary statement cases from already available recursive statement
and block classifiers. -/
def boundaryStmtCases_of_recursive
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization)
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem) :
    BoundaryStmtClassificationCases where
  skip := BoundaryClassification.skip
  exprStmt := BoundaryClassification.exprStmt
  assign := BoundaryClassification.assign
  decl := BoundaryClassification.decl
  seq := BoundaryClassification.seq stmt localControl
  ite := BoundaryClassification.ite stmt localControl
  whileStmt := BoundaryClassification.whileStmt loopBehavior
  block := BoundaryClassification.blockStmt block scopeExit
  jump := BoundaryClassification.jump

/-- Build the boundary block cases from already available recursive statement and
block classifiers. -/
def boundaryBlockCases_of_recursive
    (stmt : BoundaryStmtClassifierRealization)
    (block : BoundaryBlockClassifierRealization)
    (localControl : LocalControlRealizationTheorems) :
    BoundaryBlockClassificationCases where
  nil := BoundaryClassification.blockNil
  cons := BoundaryClassification.blockCons stmt block localControl


mutual

/-- Boundary-level statement classification constructed by structural recursion on
C++ statement syntax from local-control, scope-exit, and loop-behavior evidence. -/
def boundaryStmtClassify
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    {Γ : TypeEnv} {σ : State} :
    (st : CppStmt) → Boundary.StmtBoundary Γ σ st → Source.ClosedStmtSoundness σ st
  | .skip, boundary =>
      BoundaryClassification.skip boundary
  | .exprStmt _e, boundary =>
      BoundaryClassification.exprStmt boundary
  | .assign _a, boundary =>
      BoundaryClassification.assign boundary
  | .decl _d, boundary =>
      BoundaryClassification.decl boundary
  | .seq head tail, boundary => by
      cases boundary with
      | mk static effect safety entry =>
          cases entry with
          | seqHead headBoundary =>
              exact
                Semantics.stmtClassified_seq
                  (boundaryStmtClassify localControl scopeExit loopBehavior head headBoundary)
                  (by
                    intro σ₁ headStep
                    let seqBoundary : Boundary.StmtBoundary Γ σ (.seq head tail) :=
                      Boundary.StmtBoundary.mk static effect safety
                        (Boundary.StmtEntryEvidence.seqHead headBoundary)
                    let route : Semantics.SeqNormalRoute σ σ₁ head tail :=
                      { headNormal := headStep }
                    rcases localControl.seq.source seqBoundary route with ⟨Θ, tailControl⟩
                    let stability := Source.SeqTailControlSource.toStability tailControl
                    let tailBoundary := (Stability.SeqTailStability.tailBoundary stability).tail
                    exact boundaryStmtClassify localControl scopeExit loopBehavior tail tailBoundary)
  | .ite cond thenBranch elseBranch, boundary => by
      cases localControl.branch.select boundary with
      | thenSelected source =>
          let stability := Source.SelectedBranchControlSource.toStability source
          let selected := Stability.SelectedBranchStability.branchBoundary stability
          cases selected with
          | thenBoundary route condition preserved branchBoundary =>
              cases route with
              | thenRoute condStep =>
                  exact Semantics.stmtClassified_iteThen condStep
                    (boundaryStmtClassify localControl scopeExit loopBehavior thenBranch branchBoundary)
      | elseSelected source =>
          let stability := Source.SelectedBranchControlSource.toStability source
          let selected := Stability.SelectedBranchStability.branchBoundary stability
          cases selected with
          | elseBoundary route condition preserved branchBoundary =>
              cases route with
              | elseRoute condStep =>
                  exact Semantics.stmtClassified_iteElse condStep
                    (boundaryStmtClassify localControl scopeExit loopBehavior elseBranch branchBoundary)
  | .whileStmt cond body, boundary =>
      BoundaryClassification.whileStmt loopBehavior boundary
  | .block body, boundary => by
      cases boundary with
      | mk static effect safety entry =>
          cases entry with
          | blockOpened openedStatic openedEffect route bodyBoundary =>
              have openedEq : _ := route.opened
              subst openedEq
              let blockBoundary : Boundary.StmtBoundary Γ σ (.block body) :=
                Boundary.StmtBoundary.mk static effect safety
                  (Boundary.StmtEntryEvidence.blockOpened openedStatic openedEffect route bodyBoundary)
              exact
                Semantics.stmtClassified_block
                  (boundaryBlockClassify localControl scopeExit loopBehavior body bodyBoundary)
                  (by
                    intro r σbody bodyStep
                    rcases scopeExit.blockClose.close blockBoundary bodyBoundary route bodyStep with
                      ⟨Θ, Δ, σclosed, closeSource⟩
                    exact ⟨σclosed, closeSource.closeStep⟩)
  | .jump _j, boundary =>
      BoundaryClassification.jump boundary

/-- Boundary-level block classification constructed by structural recursion on
C++ block syntax from local-control evidence and the statement classifier above. -/
def boundaryBlockClassify
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem)
    {Γ : TypeEnv} {σ : State} :
    (body : StmtBlock) → Boundary.BlockBoundary Γ σ body → Source.ClosedBlockSoundness σ body
  | .nil, boundary =>
      BoundaryClassification.blockNil boundary
  | .cons head tail, boundary => by
      cases boundary with
      | mk static effect safety entry =>
          cases entry with
          | consHead headBoundary =>
              exact
                Semantics.blockClassified_cons
                  (boundaryStmtClassify localControl scopeExit loopBehavior head headBoundary)
                  (by
                    intro σ₁ headStep
                    let consBoundary : Boundary.BlockBoundary Γ σ (.cons head tail) :=
                      Boundary.BlockBoundary.mk static effect safety
                        (Boundary.BlockEntryEvidence.consHead headBoundary)
                    let route : Semantics.BlockConsNormalRoute σ σ₁ head tail :=
                      { headNormal := headStep }
                    rcases localControl.blockTail.source consBoundary route with ⟨Θ, tailControl⟩
                    let stability := Source.BlockTailControlSource.toStability tailControl
                    let tailBoundary := (Stability.BlockTailStability.tailBoundary stability).tail
                    exact boundaryBlockClassify localControl scopeExit loopBehavior tail tailBoundary)

end

/-- Construct both boundary-level classifiers from the lower control, scope-exit,
and loop-behavior theorem bundles.  This is the main C++ statement/block
classification realizer feeding the rest of the final route. -/
def boundaryClassifierRealization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem) :
    BoundaryClassifierRealization where
  stmt :=
    { classify := by
        intro Γ σ st boundary
        exact boundaryStmtClassify localControl scopeExit loopBehavior st boundary }
  block :=
    { classify := by
        intro Γ σ body boundary
        exact boundaryBlockClassify localControl scopeExit loopBehavior body boundary }

/-- Direct statement classifier obtained from the lower control/scope/loop bundles. -/
def boundaryStmtClassifierRealization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem) :
    BoundaryStmtClassifierRealization :=
  (boundaryClassifierRealization localControl scopeExit loopBehavior).stmt

/-- Direct block classifier obtained from the lower control/scope/loop bundles. -/
def boundaryBlockClassifierRealization
    (localControl : LocalControlRealizationTheorems)
    (scopeExit : ScopeExitRealizationTheorems)
    (loopBehavior : Source.LoopBehaviorCertificateTheorem) :
    BoundaryBlockClassifierRealization :=
  (boundaryClassifierRealization localControl scopeExit loopBehavior).block

end Realize
end Soundness2
end Cpp3
