import CppFormalization.Cpp3.Soundness.Semantic.Branch

/-!
# CppFormalization.Cpp3.Soundness.Instantiate.Providers

Explicit provider interfaces needed to instantiate the first structural
soundness clauses.

These are not global axioms.  They make the remaining cross-layer demands
visible: sequence/block-tail continuation availability, selected-branch
continuation availability, and block close availability after a finite opened
body execution.
-/

namespace Cpp3
namespace Soundness
namespace Instantiate

/-- Provides the continuation surface for a concrete normal sequence-head route. -/
structure SeqContinuationProvider : Type where
  provide :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head tail : CppStmt},
      Boundary.StmtBoundary Γ σ (.seq head tail) →
      Semantics.SeqNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          Continuation.SeqTailContinuation Γ Θ σ σ₁ head tail

/-- Provides the continuation surface for a concrete normal block-head route. -/
structure BlockTailContinuationProvider : Type where
  provide :
    ∀ {Γ : TypeEnv} {σ σ₁ : State} {head : CppStmt} {tail : StmtBlock},
      Boundary.BlockBoundary Γ σ (.cons head tail) →
      Semantics.BlockConsNormalRoute σ σ₁ head tail →
        Σ Θ : TypeEnv,
          Continuation.BlockTailContinuation Γ Θ σ σ₁ head tail

/-- Provides the selected continuation surface for an if-statement boundary. -/
structure BranchContinuationProvider : Type where
  select :
    ∀ {Γ : TypeEnv} {σ : State}
      {cond : CppCond} {thenBranch elseBranch : CppStmt},
      Boundary.StmtBoundary Γ σ (.ite cond thenBranch elseBranch) →
        (Σ Γc : TypeEnv,
          Σ σc : State,
            Continuation.ThenBranchContinuation
              Γ Γc σ σc cond thenBranch elseBranch) ⊕
        (Σ Γc : TypeEnv,
          Σ σc : State,
            Continuation.ElseBranchContinuation
              Γ Γc σ σc cond thenBranch elseBranch)

/-- Provides the block close step after a finite opened-body execution. -/
structure BlockCloseProvider : Type where
  close :
    ∀ {Γ Γopen : TypeEnv} {σ σopened : State} {body : StmtBlock}
      {r : CtrlResult} {σbody : State},
      Boundary.StmtBoundary Γ σ (.block body) →
      Boundary.BlockBoundary Γopen σopened body →
      Semantics.OpenedBlockRoute σ σopened body →
      Semantics.BigStepBlock σopened body r σbody →
        ∃ σclosed : State, popScope? σbody = some σclosed

/-- Provider bundle for the first five structural-soundness stages. -/
structure FirstFiveProviders : Type where
  seq : SeqContinuationProvider
  blockTail : BlockTailContinuationProvider
  branch : BranchContinuationProvider
  blockClose : BlockCloseProvider

end Instantiate
end Soundness
end Cpp3
