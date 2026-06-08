import CppFormalization.Cpp3.Soundness.Structural.Mutual
import CppFormalization.Cpp3.Soundness.Instantiate.While
import CppFormalization.Cpp3.Soundness.FunctionBody.Bridge

/-!
# CppFormalization.Cpp3.Soundness.Final

Final closed-fragment theorem surface.

This file does not introduce a new semantic axiom.  It packages the already
visible constructor-local providers into a `ClosedStructuralSoundnessDriver`, then
applies the mutual structural theorem.  The while reentry proof remains an
explicit provider because loop backedge classification is not a smaller-subterm
structural recursion.
-/

namespace Cpp3
namespace Soundness

namespace Instantiate

/-- Instantiate the complete structural driver from the first-five providers,
the while clause providers, and the function-body bridge. -/
def closedStructuralSoundnessDriver
    (firstFive : FirstFiveProviders)
    (whileProviders : WhileClauseProviders) :
    Structural.ClosedStructuralSoundnessDriver where
  stmt := {
    primitive := (firstFiveStmtClauses firstFive).primitive
    seq := (firstFiveStmtClauses firstFive).seq
    branch := (firstFiveStmtClauses firstFive).branch
    whileStmt := whileStructuralSoundnessClause whileProviders
    blockStmt := (firstFiveStmtClauses firstFive).blockStmt
  }
  block := {
    nil := (firstFiveBlockClauses firstFive).nil
    cons := (firstFiveBlockClauses firstFive).cons
  }
  functionBody := {
    body := FunctionBody.structuralFunctionBodyClause
  }

end Instantiate

namespace Final

/-- Provider bundle for the final closed-fragment theorem surface.

The first two fields instantiate constructor-local semantic clauses.  The last
field supplies the non-structural while-backedge classification handoff. -/
structure ClosedSoundnessProviders : Type where
  firstFive : Instantiate.FirstFiveProviders
  whileClause : Instantiate.WhileClauseProviders
  whileReentrySoundness : Structural.WhileReentrySoundnessProvider

/-- The structural driver induced by the final provider bundle. -/
def structuralDriver
    (P : ClosedSoundnessProviders) :
    Structural.ClosedStructuralSoundnessDriver :=
  Instantiate.closedStructuralSoundnessDriver P.firstFive P.whileClause

/-- Final closed statement soundness theorem, relative to the explicit providers. -/
theorem closedStmtSoundness
    (P : ClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ClosedStmtSoundness σ st :=
  Structural.closedStmtSoundness_of_structuralDriver
    (structuralDriver P)
    P.whileReentrySoundness
    st
    boundary

/-- Final closed block-body soundness theorem, relative to the explicit providers. -/
theorem closedBlockSoundness
    (P : ClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ClosedBlockSoundness σ body :=
  Structural.closedBlockSoundness_of_structuralDriver
    (structuralDriver P)
    P.whileReentrySoundness
    body
    boundary

/-- Final closed function-body soundness theorem, relative to the explicit providers. -/
theorem closedFunctionBodySoundness
    (P : ClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ClosedFunctionBodySoundness σ body :=
  Structural.closedFunctionBodySoundness_of_structuralDriver
    (structuralDriver P)
    P.whileReentrySoundness
    boundary

/-- Final statement no-unclassified-stuck theorem. -/
theorem noStmtUnclassifiedStuck
    (P : ClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {st : CppStmt}
    (boundary : Boundary.StmtBoundary Γ σ st) :
    ¬ Semantics.StmtUnclassifiedStuck σ st :=
  noStmtUnclassifiedStuck_of_closedStmtSoundness
    (closedStmtSoundness P boundary)

/-- Final block-body no-unclassified-stuck theorem. -/
theorem noBlockUnclassifiedStuck
    (P : ClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : StmtBlock}
    (boundary : Boundary.BlockBoundary Γ σ body) :
    ¬ Semantics.BlockUnclassifiedStuck σ body :=
  noBlockUnclassifiedStuck_of_closedBlockSoundness
    (closedBlockSoundness P boundary)

/-- Final function-body no-unclassified-stuck theorem. -/
theorem noFunctionBodyUnclassifiedStuck
    (P : ClosedSoundnessProviders)
    {Γ : TypeEnv} {σ : State} {body : CppStmt}
    (boundary : Boundary.FunctionBodyBoundary Γ σ body) :
    ¬ Semantics.FunctionBodyUnclassifiedStuck σ body :=
  noFunctionBodyUnclassifiedStuck_of_closedFunctionBodySoundness
    (closedFunctionBodySoundness P boundary)

end Final
end Soundness
end Cpp3
