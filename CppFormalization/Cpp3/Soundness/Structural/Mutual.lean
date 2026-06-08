import CppFormalization.Cpp3.Soundness.Structural.Driver

/-!
# CppFormalization.Cpp3.Soundness.Structural.Mutual

Mutual structural closed-soundness theorem for statements and block bodies.

The theorem is structural in the C++ syntax.  The only deliberately non-structural
piece is while reentry: after a body-normal/body-continue backedge the syntax is
again the same while-statement at a new state, so that proof cannot honestly be a
plain syntax recursion.  We therefore keep the reentry classification as an
explicit provider instead of hiding a fixed-point/coinductive argument inside the
structural driver.
-/

namespace Cpp3
namespace Soundness
namespace Structural

/-- Classification provider for while reentry handoffs.

C++ reading: when a safe loop body reaches a normal/continue backedge and the
Continuation layer reconstructs the loop-entry boundary at the reentry state,
that reentered loop state is already classified.  This is the one part of the
closed theorem that is not a smaller-subterm structural call. -/
structure WhileReentrySoundnessProvider : Type where
  sound :
    ∀ {Γ Γc : TypeEnv} {σ σreentry : State}
      {cond : CppCond} {body : CppStmt} {Reentry : Prop},
      Continuation.WhileReentryContinuation Γ Γc σ σreentry cond body Reentry →
        ClosedStmtSoundness σreentry (.whileStmt cond body)

mutual

/-- Closed statement soundness from the structural driver.

This theorem performs the actual syntax-directed recursion.  Continuation
callbacks expose post-state boundaries for smaller syntax nodes; while reentry is
routed through `WhileReentrySoundnessProvider` because it is a same-syntax
backedge rather than a structurally smaller call. -/
theorem closedStmtSoundness_of_structuralDriver
    (D : ClosedStructuralSoundnessDriver)
    (W : WhileReentrySoundnessProvider)
    {Γ : TypeEnv} {σ : State} :
    (st : CppStmt) → Boundary.StmtBoundary Γ σ st → ClosedStmtSoundness σ st
  | .skip, boundary =>
      StmtStructuralSoundnessClauses.closed_skip D.stmt boundary
  | .exprStmt _es, boundary =>
      StmtStructuralSoundnessClauses.closed_exprStmt D.stmt boundary
  | .assign _a, boundary =>
      StmtStructuralSoundnessClauses.closed_assign D.stmt boundary
  | .decl _d, boundary =>
      StmtStructuralSoundnessClauses.closed_decl D.stmt boundary
  | .seq head tail, boundary =>
      match boundary with
      | Boundary.StmtBoundary.mk static effect safety entry =>
          match entry with
          | Boundary.StmtEntryEvidence.seqHead headBoundary =>
              let wholeBoundary : Boundary.StmtBoundary Γ σ (.seq head tail) :=
                Boundary.StmtBoundary.mk static effect safety
                  (Boundary.StmtEntryEvidence.seqHead headBoundary)
              StmtStructuralSoundnessClauses.closed_seq D.stmt
                wholeBoundary
                (closedStmtSoundness_of_structuralDriver D W head headBoundary)
                (fun cont =>
                  closedStmtSoundness_of_structuralDriver D W tail
                    cont.tailBoundary)
  | .ite _cond thenBranch elseBranch, boundary =>
      StmtStructuralSoundnessClauses.closed_ite D.stmt
        boundary
        (fun cont =>
          match cont.target with
          | Boundary.SelectedBranchBoundary.thenBoundary _route _condition _preserved branchBoundary =>
              closedStmtSoundness_of_structuralDriver D W thenBranch
                branchBoundary)
        (fun cont =>
          match cont.target with
          | Boundary.SelectedBranchBoundary.elseBoundary _route _condition _preserved branchBoundary =>
              closedStmtSoundness_of_structuralDriver D W elseBranch
                branchBoundary)
  | .whileStmt _cond body, boundary =>
      StmtStructuralSoundnessClauses.closed_while D.stmt
        boundary
        (fun bodyBoundary =>
          closedStmtSoundness_of_structuralDriver D W body bodyBoundary)
        (fun cont => W.sound cont)
  | .block body, boundary =>
      StmtStructuralSoundnessClauses.closed_block D.stmt
        boundary
        (fun bodyBoundary =>
          closedBlockSoundness_of_structuralDriver D W body bodyBoundary)
  | .jump _j, boundary =>
      StmtStructuralSoundnessClauses.closed_jump D.stmt boundary

/-- Closed block-body soundness from the structural driver. -/
theorem closedBlockSoundness_of_structuralDriver
    (D : ClosedStructuralSoundnessDriver)
    (W : WhileReentrySoundnessProvider)
    {Γ : TypeEnv} {σ : State} :
    (body : StmtBlock) → Boundary.BlockBoundary Γ σ body → ClosedBlockSoundness σ body
  | .nil, boundary =>
      BlockStructuralSoundnessClauses.closed_nil D.block boundary
  | .cons head tail, boundary =>
      match boundary with
      | Boundary.BlockBoundary.mk static effect safety entry =>
          match entry with
          | Boundary.BlockEntryEvidence.consHead headBoundary =>
              let wholeBoundary : Boundary.BlockBoundary Γ σ (.cons head tail) :=
                Boundary.BlockBoundary.mk static effect safety
                  (Boundary.BlockEntryEvidence.consHead headBoundary)
              BlockStructuralSoundnessClauses.closed_cons D.block
                wholeBoundary
                (closedStmtSoundness_of_structuralDriver D W head headBoundary)
                (fun cont =>
                  closedBlockSoundness_of_structuralDriver D W tail
                    cont.tailBoundary)

end

/-- Closed function-body soundness from the same structural driver.

Function bodies are not a third recursive syntax category.  Their body is a
statement, and the function-body clause is precisely the C++-specific bridge from
statement classification to function-body classification under a
`FunctionBodyBoundary`. -/
theorem closedFunctionBodySoundness_of_structuralDriver
    (D : ClosedStructuralSoundnessDriver)
    (W : WhileReentrySoundnessProvider)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  FunctionBodyStructuralSoundnessClauses.closed_body D.functionBody
    boundary
    (fun stmtBoundary =>
      closedStmtSoundness_of_structuralDriver D W body stmtBoundary)

/-- Statement no-stuck corollary of the mutual structural theorem. -/
theorem noStmtUnclassifiedStuck_of_structuralDriver
    (D : ClosedStructuralSoundnessDriver)
    (W : WhileReentrySoundnessProvider)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_of_closedStmtSoundness
    (closedStmtSoundness_of_structuralDriver D W st boundary)

/-- Block no-stuck corollary of the mutual structural theorem. -/
theorem noBlockUnclassifiedStuck_of_structuralDriver
    (D : ClosedStructuralSoundnessDriver)
    (W : WhileReentrySoundnessProvider)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_of_closedBlockSoundness
    (closedBlockSoundness_of_structuralDriver D W body boundary)

/-- Function-body no-stuck corollary of the structural theorem. -/
theorem noFunctionBodyUnclassifiedStuck_of_structuralDriver
    (D : ClosedStructuralSoundnessDriver)
    (W : WhileReentrySoundnessProvider)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_of_closedFunctionBodySoundness
    (closedFunctionBodySoundness_of_structuralDriver D W boundary)

end Structural
end Soundness
end Cpp3
