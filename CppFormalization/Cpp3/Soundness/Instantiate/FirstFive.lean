import CppFormalization.Cpp3.Soundness.Instantiate.Providers

/-!
# CppFormalization.Cpp3.Soundness.Instantiate.FirstFive

Instantiation of the first five closed structural soundness stages:

1. primitive leaves,
2. semantic propagation,
3. sequence and block-cons structural clauses,
4. branch structural clause,
5. block-statement open/body/close clause.

The while and function-body top-level success bridge remain later stages.
-/

namespace Cpp3
namespace Soundness
namespace Instantiate

/-- Concrete sequence clause from a normal-head continuation provider. -/
def seqStructuralSoundnessClause
    (P : SeqContinuationProvider) :
    Structural.SeqStructuralSoundnessClause where
  sound := by
    intro Γ σ head tail boundary headSound tailSound
    exact
      Semantic.seq_of_classified_head headSound
        (fun route =>
          match P.provide boundary route with
          | ⟨_Θ, cont⟩ => tailSound cont)

/-- Concrete block-cons clause from a normal-head continuation provider. -/
def blockConsStructuralSoundnessClause
    (P : BlockTailContinuationProvider) :
    Structural.BlockConsStructuralSoundnessClause where
  sound := by
    intro Γ σ head tail boundary headSound tailSound
    exact
      Semantic.block_cons_of_classified_head headSound
        (fun route =>
          match P.provide boundary route with
          | ⟨_Θ, cont⟩ => tailSound cont)

/-- Concrete selected-branch clause from a selected-branch continuation provider. -/
def branchStructuralSoundnessClause
    (P : BranchContinuationProvider) :
    Structural.BranchStructuralSoundnessClause where
  sound := by
    intro Γ σ cond thenBranch elseBranch boundary thenSound elseSound
    cases P.select boundary with
    | inl selected =>
        rcases selected with ⟨Γc, σc, cont⟩
        exact Semantic.ite_then_of_continuation cont (thenSound cont)
    | inr selected =>
        rcases selected with ⟨Γc, σc, cont⟩
        exact Semantic.ite_else_of_continuation cont (elseSound cont)

/-- Concrete block-statement clause from opened-body classification plus close provider. -/
def blockStmtStructuralSoundnessClause
    (P : BlockCloseProvider) :
    Structural.BlockStmtStructuralSoundnessClause where
  sound := by
    intro Γ σ body boundary bodySound
    cases boundary with
    | mk _static _effect _safety entry =>
        cases entry with
        | blockOpened _openedStatic _openedEffect route bodyBoundary =>
            have hbody : ClosedBlockSoundness _ body :=
              bodySound bodyBoundary
            exact
              Semantic.block_stmt_of_opened_body route hbody
                (fun bodyStep =>
                  P.close
                    (Boundary.StmtBoundary.mk _static _effect _safety
                      (Boundary.StmtEntryEvidence.blockOpened
                        _openedStatic _openedEffect route bodyBoundary))
                    bodyBoundary
                    route
                    bodyStep)

/-- Concrete nil-block clause. -/
def blockNilStructuralSoundnessClause :
    Structural.BlockNilStructuralSoundnessClause where
  sound := by
    intro Γ σ boundary
    exact Semantic.block_nil boundary

/-- The first-five statement clauses, except for while which remains later. -/
structure FirstFiveStmtClauses : Type where
  primitive : Structural.PrimitiveStmtSoundnessClauses
  seq : Structural.SeqStructuralSoundnessClause
  branch : Structural.BranchStructuralSoundnessClause
  blockStmt : Structural.BlockStmtStructuralSoundnessClause

/-- The first-five block clauses. -/
structure FirstFiveBlockClauses : Type where
  nil : Structural.BlockNilStructuralSoundnessClause
  cons : Structural.BlockConsStructuralSoundnessClause

/-- Instantiate the first-five statement clauses from explicit providers. -/
def firstFiveStmtClauses
    (P : FirstFiveProviders) : FirstFiveStmtClauses where
  primitive := Primitive.primitiveStmtSoundnessClauses
  seq := seqStructuralSoundnessClause P.seq
  branch := branchStructuralSoundnessClause P.branch
  blockStmt := blockStmtStructuralSoundnessClause P.blockClose

/-- Instantiate the first-five block clauses from explicit providers. -/
def firstFiveBlockClauses
    (P : FirstFiveProviders) : FirstFiveBlockClauses where
  nil := blockNilStructuralSoundnessClause
  cons := blockConsStructuralSoundnessClause P.blockTail

end Instantiate
end Soundness
end Cpp3
